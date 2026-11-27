"""Runtime wiring shared by the compiler command and smoke runner."""

from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import select
import shutil
import signal
import subprocess
import tempfile
import time

REPO = Path(__file__).resolve().parents[1]
PIN = "7b1f02b09954b9b916eb2a91d283c9b5355bf172"
SWITCH = "compcert-3.17"
ALLOCATOR = "irc"
BUILD = REPO / ".lake" / "prototype"
LEAN = REPO / ".lake" / "build" / "bin" / "leanCompiler"
def reference_flags(optimization="O0"):
    if optimization not in {"O0", "O2"}:
        raise ValueError("unsupported normalized optimization profile")
    enabled = optimization == "O2"
    prefix = "-f" if enabled else "-fno-"
    return ["-" + optimization, prefix + "inline", prefix + "inline-functions-called-once",
            prefix + "if-conversion", "-ffloat-const-prop", "2" if enabled else "0",
            "-fno-pic", "-fno-pie", "-fno-common"]


REFERENCE_FLAGS = reference_flags()


class CompileError(RuntimeError):
    def __init__(self, message, *, stage=None, category=None, timed_out=False):
        super().__init__(message)
        self.stage = stage
        self.category = category
        self.timed_out = timed_out


def revision(root):
    return execute(["git", "-C", root, "rev-parse", "HEAD"]).decode().strip()


def terminate(process):
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


def execute(command, *, cwd=None, timeout=None, env=None, log=None, stdin=None):
    command = [str(argument) for argument in command]
    started = time.monotonic()
    process = subprocess.Popen(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL,
                               start_new_session=True)
    timed_out = False
    try:
        stdout, stderr = process.communicate(input=stdin, timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        terminate(process)
        stdout, stderr = process.communicate()
    result = {"command": command, "cwd": str(cwd or Path.cwd()),
              "returncode": process.returncode, "timeout": timed_out,
              "seconds": time.monotonic() - started}
    if log:
        log = Path(log)
        log.with_suffix(".stdout").write_bytes(stdout)
        log.with_suffix(".stderr").write_bytes(stderr)
        log.with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    if timed_out or process.returncode:
        detail = "timed out" if timed_out else f"exited {process.returncode}"
        raise CompileError(f"{command[0]} {detail}: {stderr.decode(errors='replace')[-6000:]}", timed_out=timed_out)
    return stdout


def tool_environment(root):
    return {**os.environ, "COMPCERT_CONFIG": str(root / "compcert.ini")}


def prepare(root, *, lean_session=None):
    if lean_session is not None:
        lean_session.close()
    try:
        return prepare_toolchain(root, lean_session)
    except BaseException:
        if lean_session is not None:
            lean_session.close()
        raise


def prepare_toolchain(root, lean_session):
    root = Path(root).resolve()
    if revision(root) != PIN:
        raise CompileError(f"CompCert must be pinned at {PIN}")
    BUILD.mkdir(parents=True, exist_ok=True)
    version_commands = {
        "ocaml_tools": ["opam", "exec", "--switch=" + SWITCH, "--", "sh", "-c",
                        "ocamlopt -version && ocamlfind query -format '%v' yojson"],
        "gcc": ["gcc", "--version"],
        "compcert": [root / "ccomp", "-version"],
    }
    with ThreadPoolExecutor(max_workers=len(version_commands) + 1) as executor:
        lean_build = executor.submit(execute, ["lake", "build", "leanCompiler"],
                                     cwd=REPO, log=BUILD / "lean-build")
        outputs = executor.map(
            lambda command: execute(command, cwd=REPO, env=tool_environment(root)).decode().strip(),
            version_commands.values())
        versions = dict(zip(version_commands, outputs))
        lean_build.result()
        versions["lean"] = (execute([LEAN, "--version"], cwd=REPO).decode().strip() if lean_session is None
                            else lean_session.version(deadline=time.monotonic() + 300))
        ocaml_tools = versions.pop("ocaml_tools").splitlines()
        if len(ocaml_tools) != 2:
            raise CompileError("invalid OCaml tool version output: " + repr(ocaml_tools))
        versions["ocaml"], versions["yojson"] = ocaml_tools
        lean_version = (REPO / "lean-toolchain").read_text().strip().rsplit(":v", 1)[-1]
        if (lean_version not in versions["lean"] or not versions["ocaml"].startswith("4.14.")
                or versions["yojson"].split(".")[0] not in ("2", "3")):
            raise CompileError(f"expected Lean {lean_version}, OCaml 4.14 and yojson 2 or 3: " + repr(versions))
    bridge_dir = BUILD / "bridge"
    bridge_dir.mkdir(exist_ok=True)
    sources = [REPO / "bridge" / filename for filename in ("primitives.ml", "codecs.ml", "bridge.ml")]
    includes = [root / directory for directory in
                ("extraction", "lib", "common", "x86", "backend", "cfrontend", "cparser", "driver", "export", "debug")]
    objects = execute([root / "tools/modorder", ".depend.extr", "driver/CommonOptions.cmx",
                       "driver/Frontend.cmx", "backend/PrintAsm.cmx", "x86/Asmexpand.cmx"], cwd=root).decode().split()
    digest = hashlib.sha256()
    digest.update(str(root).encode())
    for path in [*sources, *(root / name for name in objects)]:
        digest.update(path.read_bytes())
    stamp = bridge_dir / "fingerprint"
    bridge = bridge_dir / "bridge"
    if not bridge.exists() or not stamp.exists() or stamp.read_text() != digest.hexdigest():
        for source in sources:
            shutil.copy2(source, bridge_dir / source.name)
        command = ["opam", "exec", "--switch=" + SWITCH, "--", "ocamlfind", "ocamlopt",
                   "-package", "yojson,zarith,menhirLib,str,unix", "-linkpkg",
                   *[argument for directory in includes for argument in ("-I", directory)],
                   *[root / name for name in objects], *[source.name for source in sources], "-o", bridge]
        execute(command, cwd=bridge_dir, log=BUILD / "bridge-build")
        stamp.write_text(digest.hexdigest())
    versions.update({"compcert_revision": PIN, "lean_revision": revision(REPO), "allocator": ALLOCATOR})
    versions["prototype_sha256"] = {str(path.relative_to(REPO)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted([REPO / "lakefile.toml", *REPO.glob("CompCert4Lean/Prototype/*.lean"),
                            *REPO.glob("CompCert4Lean/Allocator/*.lean"),
                            *REPO.glob("bridge/*.ml"), *REPO.glob("scripts/*.py")])}
    (BUILD / "versions.json").write_text(json.dumps(versions, indent=2) + "\n")
    return versions


class Bridge:
    def __init__(self, root, folder, deadline):
        self.deadline = deadline
        self.buffer = b""
        self.stderr_path = folder / "bridge.stderr"
        self.stderr = (folder / "bridge.stderr").open("wb")
        command = [str(BUILD / "bridge" / "bridge")]
        (folder / "bridge-command.json").write_text(json.dumps(command) + "\n")
        self.process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=self.stderr, env=tool_environment(root), start_new_session=True)
        self.transcript = (folder / "bridge-protocol.jsonl").open("w")

    def request(self, data, *, deadline=None):
        deadline = self.deadline if deadline is None else deadline
        self.transcript.write(json.dumps({"request": data}) + "\n")
        self.transcript.flush()
        try:
            self.process.stdin.write((json.dumps(data) + "\n").encode())
            self.process.stdin.flush()
            while b"\n" not in self.buffer:
                remaining = deadline - time.monotonic()
                if remaining <= 0 or not select.select([self.process.stdout], [], [], remaining)[0]:
                    raise CompileError("CompCert bridge timed out", timed_out=True)
                chunk = os.read(self.process.stdout.fileno(), 65536)
                if not chunk:
                    detail = self.stderr_path.read_text(errors="replace")[-6000:]
                    raise CompileError("CompCert bridge failed: " + detail)
                self.buffer += chunk
            line, self.buffer = self.buffer.split(b"\n", 1)
            response = json.loads(line)
            self.transcript.write(json.dumps({"response": response}) + "\n")
            self.transcript.flush()
            if not isinstance(response, dict):
                raise CompileError("CompCert bridge protocol error: invalid response")
            if response.get("ok") is not True:
                raise CompileError("CompCert bridge rejected request: " + repr(response))
        except (BrokenPipeError, json.JSONDecodeError) as error:
            raise CompileError("CompCert bridge protocol error: " + str(error)) from error

    def close(self):
        terminate(self.process)
        self.process.stdin.close()
        self.process.stdout.close()
        self.stderr.close()
        self.transcript.close()


class BridgeServer:
    def __init__(self, root, folder):
        self.root = Path(root).resolve()
        self.folder = Path(folder).resolve()
        self.folder.mkdir(parents=True, exist_ok=True)
        self.buffer = b""
        self.process = None
        self.cwd = None
        self.stderr_path = self.folder / "bridge-server.stderr"
        self.stderr = self.stderr_path.open("ab")
        self.transcript = (self.folder / "bridge-server-protocol.jsonl").open("a")
        self.command = [str(BUILD / "bridge" / "bridge")]
        (self.folder / "bridge-server-command.json").write_text(json.dumps(self.command) + "\n")

    def start(self):
        cwd = Path.cwd()
        if self.process is not None and self.cwd != cwd:
            self.reset()
        if self.process is not None:
            return
        environment = {**tool_environment(self.root), "COMPCERT4LEAN_BRIDGE_SERVER": "1"}
        self.process = subprocess.Popen(self.command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=self.stderr, env=environment, cwd=cwd, start_new_session=True)
        self.cwd = cwd

    def request(self, data, *, deadline):
        try:
            if deadline <= time.monotonic():
                raise CompileError("CompCert bridge timed out", timed_out=True)
            self.start()
            self.transcript.write(json.dumps({"request": data, "pid": self.process.pid,
                                             "cwd": str(self.cwd)}) + "\n")
            self.transcript.flush()
            self.process.stdin.write((json.dumps(data) + "\n").encode())
            self.process.stdin.flush()
            while b"\n" not in self.buffer:
                remaining = deadline - time.monotonic()
                if remaining <= 0 or not select.select([self.process.stdout], [], [], remaining)[0]:
                    raise CompileError("CompCert bridge timed out", timed_out=True)
                chunk = os.read(self.process.stdout.fileno(), 65536)
                if not chunk:
                    detail = self.stderr_path.read_text(errors="replace")[-6000:]
                    raise CompileError("CompCert bridge failed: " + detail)
                self.buffer += chunk
            line, self.buffer = self.buffer.split(b"\n", 1)
            response = json.loads(line)
            self.transcript.write(json.dumps({"response": response}) + "\n")
            self.transcript.flush()
            if not isinstance(response, dict):
                raise CompileError("CompCert bridge protocol error: invalid response")
            if response.get("ok") is not True:
                detail = self.stderr_path.read_text(errors="replace")[-6000:]
                raise CompileError("CompCert bridge rejected request: " + repr(response) + "\n" + detail)
            expected = "assembly" if data.get("operation") == "print" else "frontend"
            if response.get("phase") != expected:
                raise CompileError("CompCert bridge protocol error: unexpected phase")
        except (OSError, json.JSONDecodeError) as error:
            self.reset()
            raise CompileError("CompCert bridge protocol error: " + str(error)) from error
        except BaseException:
            self.reset()
            raise

    def reset(self):
        if self.process is None:
            return
        terminate(self.process)
        self.process.stdin.close()
        self.process.stdout.close()
        self.process = None
        self.cwd = None
        self.buffer = b""

    def close(self):
        self.reset()
        self.stderr.close()
        self.transcript.close()


class LeanSession:
    def __init__(self, folder):
        self.folder = Path(folder).resolve()
        self.process = None
        self.stderr = None
        self.buffer = b""

    def start(self):
        if self.process is not None:
            return
        self.folder.mkdir(parents=True, exist_ok=True)
        self.stderr = (self.folder / "lean-server.stderr").open("ab")
        try:
            self.process = subprocess.Popen([str(LEAN), "--server"], cwd=REPO,
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.stderr, start_new_session=True)
        except BaseException:
            self.stderr.close()
            self.stderr = None
            raise

    def request(self, request, *, deadline, log):
        started = time.monotonic()
        record = {"command": [str(LEAN), "--server"], "cwd": str(REPO), "request": request,
                  "returncode": 1, "timeout": False}
        stderr = b""
        try:
            if deadline <= time.monotonic():
                raise CompileError("Lean compiler timed out", timed_out=True)
            self.start()
            record["pid"] = self.process.pid
            self.process.stdin.write((json.dumps(request) + "\n").encode())
            self.process.stdin.flush()
            while b"\n" not in self.buffer:
                remaining = deadline - time.monotonic()
                if remaining <= 0 or not select.select([self.process.stdout], [], [], remaining)[0]:
                    raise CompileError("Lean compiler timed out", timed_out=True)
                chunk = os.read(self.process.stdout.fileno(), 65536)
                if not chunk:
                    detail = (self.folder / "lean-server.stderr").read_text(errors="replace")[-6000:]
                    raise CompileError("Lean compiler server failed: " + detail)
                self.buffer += chunk
            line, self.buffer = self.buffer.split(b"\n", 1)
            response = json.loads(line)
            if not isinstance(response, dict) or response.get("ok") is not True:
                message = response.get("error", "invalid response") if isinstance(response, dict) else "invalid response"
                raise CompileError("Lean compiler rejected input: " + str(message))
            if request.get("operation") == "version" and not isinstance(response.get("version"), str):
                raise CompileError("Lean compiler protocol error: missing runtime version")
            record["returncode"] = 0
            return response
        except (BrokenPipeError, json.JSONDecodeError) as error:
            stderr = str(error).encode()
            self.close()
            raise CompileError("Lean compiler protocol error: " + str(error)) from error
        except BaseException as error:
            stderr = str(error).encode()
            record["timeout"] = getattr(error, "timed_out", False)
            self.close()
            raise
        finally:
            record["seconds"] = time.monotonic() - started
            log = Path(log)
            log.with_suffix(".stdout").write_bytes(b"")
            log.with_suffix(".stderr").write_bytes(stderr)
            log.with_suffix(".json").write_text(json.dumps(record, indent=2) + "\n")

    def compile(self, source, target, *, deadline, log):
        request = {"input": str(Path(source).resolve()), "output": str(Path(target).resolve())}
        self.request(request, deadline=deadline, log=log)

    def version(self, *, deadline):
        self.folder.mkdir(parents=True, exist_ok=True)
        return self.request({"operation": "version"}, deadline=deadline,
                            log=self.folder / "lean-version")["version"]

    def close(self):
        if self.process is not None:
            terminate(self.process)
            self.process.stdin.close()
            self.process.stdout.close()
            self.stderr.close()
            self.process = None
            self.stderr = None
            self.buffer = b""


def validate_inputs(options):
    inputs = [Path(value).resolve() for kind, value in options.inputs if kind == "input"]
    for source in inputs:
        if not source.is_file():
            raise CompileError(f"input does not exist: {source}")
        if source.suffix not in {".c", ".s", ".S", ".o", ".a", ".so"} and ".so." not in source.name:
            raise CompileError(f"unsupported input: {source}")
        if options.assembly and source.suffix != ".c":
            raise CompileError("-S requires C source inputs")
        if options.object and source.suffix not in {".c", ".s", ".S"}:
            raise CompileError("-c requires C or assembly inputs")
    outputs = ([options.output.resolve()] if options.output else
               [Path(source.stem + (".s" if options.assembly else ".o")).resolve() for source in inputs])
    if len(set(outputs)) != len(outputs):
        raise CompileError("output-name collision; compile these inputs separately with -o")
    if any(output in inputs for output in outputs):
        raise CompileError("output must differ from every input")
    for output in outputs:
        if output.is_dir() or not output.parent.is_dir():
            raise CompileError(f"invalid output path: {output}")
    return inputs, outputs


def publish_output(source, output):
    descriptor, temporary = tempfile.mkstemp(prefix="." + output.name + "-", dir=output.parent)
    os.close(descriptor)
    try:
        shutil.copy2(source, temporary)
        os.replace(temporary, output)
    finally:
        Path(temporary).unlink(missing_ok=True)


def compile_source(options, *, prepared=False, artifact_dir=None, timeout=None, lean_session=None,
                   bridge_session=None):
    root = options.compcert_root.resolve()
    inputs, outputs = validate_inputs(options)
    BUILD.mkdir(parents=True, exist_ok=True)
    folder = Path(artifact_dir) if artifact_dir else Path(tempfile.mkdtemp(prefix="compile-", dir=BUILD))
    folder = folder.resolve()
    folder.mkdir(parents=True, exist_ok=True)
    owns_session = lean_session is None and sum(source.suffix == ".c" for source in inputs) > 1
    if owns_session:
        lean_session = LeanSession(folder)
    try:
        if not prepared:
            prepare(root, lean_session=lean_session)
        timeout = options.compile_timeout if timeout is None else timeout
        if timeout <= 0:
            raise CompileError("compilation timeout must be positive")
        versions = json.loads((BUILD / "versions.json").read_text())
        metadata = {"inputs": options.inputs, "input_sha256": {str(source): hashlib.sha256(source.read_bytes()).hexdigest() for source in inputs},
                    "outputs": list(map(str, outputs)), "allocator": ALLOCATOR, "timeout_seconds": timeout,
                    "configuration": {"pic": options.pic, "pie": False, "common": options.common,
                                      "optimization": options.optimization},
                    "standard": options.std,
                    "language": options.language, "preprocessor": options.preprocessor, "stages": [],
                    "versions": versions, "success": False}
    except BaseException:
        if owns_session:
            lean_session.close()
        raise
    stage = "frontend"
    def record(name, action):
        nonlocal stage
        stage = name
        started = time.monotonic()
        try:
            result = action()
        except Exception as error:
            metadata["stages"].append({"stage": name, "input": str(source) if name != "link" else None,
                                       "status": "timeout" if getattr(error, "timed_out", False) else "failed",
                                       "seconds": time.monotonic() - started, "error": str(error)})
            raise
        metadata["stages"].append({"stage": name, "input": str(source) if name != "link" else None,
                                   "status": "passed", "seconds": time.monotonic() - started})
        return result
    owns_bridge_session = bridge_session is None and sum(source.suffix == ".c" for source in inputs) > 1
    try:
        if owns_bridge_session:
            bridge_session = BridgeServer(root, folder)
        built = []
        for index, source in enumerate(inputs):
            unit = folder if len(inputs) == 1 else folder / f"unit-{index:03d}-{source.stem}"
            unit.mkdir(exist_ok=True)
            generated = source
            if source.suffix == ".c":
                deadline = time.monotonic() + timeout
                bridge = bridge_session or Bridge(root, unit, deadline)
                try:
                    record("frontend", lambda: bridge.request({"root": str(root), "source": str(source),
                           "preprocessor": options.preprocessor, "language": options.language,
                           "standard": options.std,
                           "configuration": metadata["configuration"],
                           "preprocessed": str(unit / "input.i"), "csyntax": str(unit / "csyntax.json")},
                           deadline=deadline))
                    if lean_session is None:
                        record("lean", lambda: execute([LEAN, unit / "csyntax.json", unit / "asm.json"], cwd=REPO,
                               timeout=max(0.001, deadline - time.monotonic()), log=unit / "lean"))
                    else:
                        record("lean", lambda: lean_session.compile(unit / "csyntax.json", unit / "asm.json",
                               deadline=deadline, log=unit / "lean"))
                    record("assembly_print", lambda: bridge.request({"operation": "print", "input": str(unit / "asm.json"),
                           "output": str(unit / "output.s")}, deadline=deadline))
                    generated = unit / "output.s"
                except BaseException:
                    if bridge_session is not None:
                        bridge_session.reset()
                    raise
                finally:
                    if bridge_session is None:
                        bridge.close()
            if not options.assembly and source.suffix in {".c", ".s", ".S"}:
                assembly = generated
                generated = unit / "output.o"
                record("assemble", lambda: execute(["gcc", "-m64", "-c", *options.preprocessor,
                       assembly, "-o", generated], timeout=options.link_timeout, log=unit / "assemble"))
            built.append(generated)
        if options.assembly or options.object:
            publications = list(zip(built, outputs))
        else:
            compiled = iter(built)
            arguments = [str(next(compiled)) if kind == "input" else value for kind, value in options.inputs]
            generated = folder / "output"
            mode = "-shared" if options.shared else "-r" if options.relocatable else "-no-pie"
            runtime = [] if options.relocatable else [root / "runtime/libcompcert.a"]
            record("link", lambda: execute(["gcc", "-m64", mode, *arguments, *runtime, "-o", generated],
                   timeout=options.link_timeout, log=folder / "link"))
            publications = [(generated, outputs[0])]
        for generated, output in publications:
            publish_output(generated, output)
        metadata["success"] = True
    except Exception as error:
        metadata["error"] = str(error)
        timed_out = getattr(error, "timed_out", False)
        category = "timeout" if timed_out else {"frontend": "frontend_rejection", "lean": "lean_rejection",
                    "assembly_print": "assembly_failure", "assemble": "assembly_failure", "link": "link_failure"}.get(stage, "harness_failure")
        metadata.update(stage=stage, category=category)
        raise CompileError(f"{error}\nArtifacts: {folder}", stage=stage, category=category, timed_out=timed_out) from error
    finally:
        if owns_session:
            lean_session.close()
        if owns_bridge_session and bridge_session is not None:
            bridge_session.close()
        (folder / "result.json").write_text(json.dumps(metadata, indent=2) + "\n")
    if not options.keep_temps and artifact_dir is None:
        shutil.rmtree(folder)
    return folder
