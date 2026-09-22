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
    pass


def revision(root):
    return execute(["git", "-C", root, "rev-parse", "HEAD"]).decode().strip()


def terminate(process):
    if process.poll() is None:
        os.killpg(process.pid, signal.SIGKILL)
    process.wait()


def execute(command, *, cwd=None, timeout=None, env=None, log=None):
    command = [str(argument) for argument in command]
    started = time.monotonic()
    process = subprocess.Popen(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, start_new_session=True)
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=timeout)
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
        raise CompileError(f"{command[0]} {detail}: {stderr.decode(errors='replace')[-6000:]}")
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
                    raise CompileError("CompCert bridge timed out")
                chunk = os.read(self.process.stdout.fileno(), 65536)
                if not chunk:
                    raise CompileError("CompCert bridge failed; see bridge.stderr")
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
        self.stderr.close()
        self.transcript.close()


def compile_source(options, *, prepared=False, artifact_dir=None, timeout=120):
    root = options.compcert_root.resolve()
    if not prepared:
        prepare(root)
    if timeout <= 0:
        raise CompileError("compilation timeout must be positive")
    source = options.source.resolve()
    output = options.output.resolve()
    if source == output:
        raise CompileError("output must differ from source")
    if not source.is_file():
        raise CompileError(f"source does not exist: {source}")
    folder = Path(artifact_dir) if artifact_dir else Path(tempfile.mkdtemp(prefix="compile-", dir=BUILD))
    folder.mkdir(parents=True, exist_ok=True)
    preprocessor = options.preprocessor
    metadata = {"source": str(source), "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                "output": str(output), "allocator": ALLOCATOR, "timeout_seconds": timeout,
                "versions": json.loads((BUILD / "versions.json").read_text()), "success": False}
    deadline = time.monotonic() + timeout
    bridge = None
    try:
        bridge = Bridge(root, folder, deadline)
        bridge.request({"root": str(root), "source": str(source), "preprocessor": preprocessor,
                        "preprocessed": str(folder / "input.i"), "csyntax": str(folder / "csyntax.json")})
        execute([LEAN, folder / "csyntax.json", folder / "asm.json"], cwd=REPO,
                timeout=max(0.001, deadline - time.monotonic()), log=folder / "lean")
        bridge.request({"operation": "print", "input": str(folder / "asm.json"), "output": str(folder / "output.s")})
        bridge.process.wait(timeout=max(0.001, deadline - time.monotonic()))
        if bridge.process.returncode:
            raise CompileError("CompCert assembly printer failed")
        generated = folder / "output.s"
        if not options.assembly:
            generated = folder / ("output.o" if options.object else "output")
            command = ["gcc", "-m64", "-fno-pic", "-fno-pie", "-fno-common"]
            command += ["-c"] if options.object else ["-no-pie"]
            command += [folder / "output.s", "-o", generated]
            if not options.object:
                command += ["-L" + value for value in options.library_path]
                command += [root / "runtime/libcompcert.a", *["-l" + value for value in options.library]]
            execute(command, timeout=max(0.001, deadline - time.monotonic()), log=folder / "gcc")
        if generated.resolve() != output:
            shutil.copy2(generated, output)
        metadata["success"] = True
    except Exception as error:
        metadata["error"] = str(error)
        raise CompileError(f"{error}\nArtifacts: {folder}") from error
    finally:
        if bridge:
            bridge.close()
        (folder / "result.json").write_text(json.dumps(metadata, indent=2) + "\n")
    if not options.keep_temps and artifact_dir is None:
        shutil.rmtree(folder)
    return folder
