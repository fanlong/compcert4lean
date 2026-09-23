"""Runtime wiring shared by the compiler command and smoke runner."""

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
ALLOCATOR = "spill"
BUILD = REPO / ".lake" / "prototype"
LEAN = REPO / ".lake" / "build" / "bin" / "leanCompiler"
REFERENCE_FLAGS = ["-O0", "-fno-inline", "-fno-inline-functions-called-once",
                   "-fno-if-conversion", "-ffloat-const-prop", "0",
                   "-fno-pic", "-fno-pie", "-fno-common"]


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


def prepare(root):
    root = Path(root).resolve()
    if revision(root) != PIN:
        raise CompileError(f"CompCert must be pinned at {PIN}")
    BUILD.mkdir(parents=True, exist_ok=True)
    versions = {}
    for name, command in {
        "lean": ["lake", "env", "lean", "--version"],
        "ocaml": ["opam", "exec", "--switch=" + SWITCH, "--", "ocamlopt", "-version"],
        "yojson": ["opam", "exec", "--switch=" + SWITCH, "--", "ocamlfind", "query", "-format", "%v", "yojson"],
        "gcc": ["gcc", "--version"],
        "compcert": [root / "ccomp", "-version"],
    }.items():
        versions[name] = execute(command, cwd=REPO, env=tool_environment(root)).decode().strip()
    if "4.33.0" not in versions["lean"] or versions["ocaml"] != "4.14.2" or versions["yojson"] != "2.2.2":
        raise CompileError("expected Lean 4.33.0, OCaml 4.14.2 and yojson 2.2.2: " + repr(versions))
    execute(["lake", "build", "leanCompiler"], cwd=REPO, log=BUILD / "lean-build")
    bridge_dir = BUILD / "bridge"
    bridge_dir.mkdir(exist_ok=True)
    sources = [REPO / "bridge" / filename for filename in ("primitives.ml", "codecs.ml", "bridge.ml")]
    includes = [root / directory for directory in
                ("extraction", "lib", "common", "x86", "backend", "cfrontend", "cparser", "driver", "export", "debug")]
    objects = execute([root / "tools/modorder", ".depend.extr", "driver/Frontend.cmx",
                       "backend/PrintAsm.cmx", "x86/Asmexpand.cmx"], cwd=root).decode().split()
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

    def request(self, data):
        self.transcript.write(json.dumps({"request": data}) + "\n")
        self.transcript.flush()
        try:
            self.process.stdin.write((json.dumps(data) + "\n").encode())
            self.process.stdin.flush()
            while b"\n" not in self.buffer:
                remaining = self.deadline - time.monotonic()
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


def compile_source(options, *, prepared=False, artifact_dir=None, timeout=None):
    root = options.compcert_root.resolve()
    inputs, outputs = validate_inputs(options)
    if not prepared:
        prepare(root)
    timeout = options.compile_timeout if timeout is None else timeout
    if timeout <= 0:
        raise CompileError("compilation timeout must be positive")
    folder = Path(artifact_dir) if artifact_dir else Path(tempfile.mkdtemp(prefix="compile-", dir=BUILD))
    folder = folder.resolve()
    folder.mkdir(parents=True, exist_ok=True)
    metadata = {"inputs": options.inputs, "input_sha256": {str(source): hashlib.sha256(source.read_bytes()).hexdigest() for source in inputs},
                "outputs": list(map(str, outputs)), "allocator": ALLOCATOR, "timeout_seconds": timeout,
                "configuration": {"pic": options.pic, "pie": False, "common": options.common},
                "language": options.language, "preprocessor": options.preprocessor, "stages": [],
                "versions": json.loads((BUILD / "versions.json").read_text()), "success": False}
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
    try:
        built = []
        for index, source in enumerate(inputs):
            unit = folder if len(inputs) == 1 else folder / f"unit-{index:03d}-{source.stem}"
            unit.mkdir(exist_ok=True)
            generated = source
            if source.suffix == ".c":
                deadline = time.monotonic() + timeout
                bridge = Bridge(root, unit, deadline)
                try:
                    record("frontend", lambda: bridge.request({"root": str(root), "source": str(source),
                           "preprocessor": options.preprocessor, "language": options.language,
                           "configuration": metadata["configuration"],
                           "preprocessed": str(unit / "input.i"), "csyntax": str(unit / "csyntax.json")}))
                    record("lean", lambda: execute([LEAN, unit / "csyntax.json", unit / "asm.json"], cwd=REPO,
                           timeout=max(0.001, deadline - time.monotonic()), log=unit / "lean"))
                    record("assembly_print", lambda: bridge.request({"operation": "print", "input": str(unit / "asm.json"),
                           "output": str(unit / "output.s")}))
                    generated = unit / "output.s"
                finally:
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
        (folder / "result.json").write_text(json.dumps(metadata, indent=2) + "\n")
    if not options.keep_temps and artifact_dir is None:
        shutil.rmtree(folder)
    return folder
