import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import uuid


sys.dont_write_bytecode = True
REPO = Path(__file__).resolve().parents[1]
META = REPO.parent
TASK = REPO
EVIDENCE = REPO / ".lake" / "prototype" / "guard"
EVIDENCE.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(META / "scripts"))
import compute_sandbox as containment


def child(folder):
    request = containment.read_json(folder / "REQUEST.json")
    containment.kernel_guard(containment.cgroup(), containment.MEMORY_MAX)
    invocation = os.environ["INVOCATION_ID"]
    containment.write_new(folder / "READY.json", {
        "identity": containment.identity(os.getpid()), "invocation": invocation,
    })
    deadline = time.monotonic() + 30
    while not (folder / "ADMISSION.json").exists():
        containment.require(time.monotonic() < deadline, "Startup admission timed out")
        time.sleep(0.05)
    admission = containment.read_json(folder / "ADMISSION.json")
    containment.require(admission["invocation"] == invocation, "Compute invocation changed")
    containment.require(containment.same_live(request["supervisor"]), "Supervisor disappeared")
    containment.kernel_guard(containment.cgroup(), containment.MEMORY_MAX)
    if request["command"] == ["--install-yojson"]:
        os.execvp("opam", ["opam", "install", "--switch=compcert-3.17", "yojson.2.2.2", "-y"])
    command = [
        "bwrap", "--die-with-parent", "--unshare-pid", "--unshare-net", "--unshare-ipc",
        "--cap-drop", "ALL", "--ro-bind", "/", "/",
        "--bind", str(TASK), str(TASK),
        "--bind", str(EVIDENCE), str(EVIDENCE),
        "--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp", "--tmpfs", "/run",
        "--ro-bind", str(Path("/etc/resolv.conf").resolve()), str(Path("/etc/resolv.conf").resolve()),
        "--ro-bind", "/dev/null", str(META / "openai.key"),
        "--ro-bind", "/dev/null", str(META / "openai2.key"),
        "--ro-bind", "/dev/null", str(META / "openai3.key"),
        "--ro-bind", "/dev/null", str(META / "claude.key"),
        "--chdir", str(REPO), "--", *request["command"],
    ]
    os.execvp(command[0], command)


def supervise(command):
    configuration = containment.config()
    with (containment.RUNS / "lifecycle.lock").open("rb") as lock:
        print("Acquiring the shared compute domain", flush=True)
        fcntl.flock(lock, fcntl.LOCK_EX)
        containment.require(not (containment.RUNS / "ACTIVE.json").exists(), "An existing compute invocation needs review")
        containment.require(containment.service_status().get("LoadState") == "not-found", "Shared compute service is occupied")
        headroom = containment.host_headroom(containment.MEMORY_MAX, configuration)
        protected = containment.protected_processes()
        folder = EVIDENCE / "compute" / (time.strftime("%Y%m%dT%H%M%S", time.gmtime()) + "-" + uuid.uuid4().hex[:8])
        folder.mkdir(parents=True)
        paths = subprocess.check_output(["git", "-C", str(REPO), "ls-files", "--cached", "--others", "--exclude-standard", "-z"]).decode().split("\0")
        request = {
            "command": command, "started_epoch": time.time(), "host_headroom": headroom,
            "supervisor": containment.identity(os.getpid()), "protected": protected,
            "source_hashes": {name: hashlib.sha256((REPO / name).read_bytes()).hexdigest()
                              if (REPO / name).is_file() else None for name in paths if name},
        }
        inputs = folder / "inputs"
        inputs.mkdir()
        request["inputs"] = {}
        for source in Path(__file__).resolve().parent.iterdir():
            if source.suffix in {".lean", ".py"}:
                content = source.read_bytes()
                (inputs / source.name).write_bytes(content)
                request["inputs"][source.name] = hashlib.sha256(content).hexdigest()
        containment.write_new(folder / "REQUEST.json", request)
        properties = {**configuration["service_properties"], "WorkingDirectory": str(REPO),
                      "StandardOutput": "append:" + str(folder / "stdout.log"),
                      "StandardError": "append:" + str(folder / "stderr.log")}
        launch = [
            "systemd-run", "--user", "--unit=" + containment.UNIT, "--expand-environment=no",
            "--setenv=PATH=" + os.environ["PATH"], "--setenv=PYTHONDONTWRITEBYTECODE=1",
            *["--property=" + name + "=" + value for name, value in properties.items()],
            "--", sys.executable, "-B", str(Path(__file__).resolve()), "_child", str(folder),
        ]
        print(str(folder), flush=True)
        containment.command(launch)
        group = None
        recorded = {}
        state = {}
        try:
            deadline = time.monotonic() + 30
            while not (folder / "READY.json").exists():
                state = containment.service_status()
                containment.require(state.get("ActiveState") not in {"failed", "inactive"}
                                    and time.monotonic() < deadline, "Compute startup failed")
                time.sleep(0.05)
            state = containment.service_status()
            ready = containment.read_json(folder / "READY.json")
            group = containment.CGROUP_ROOT / state["ControlGroup"].lstrip("/")
            containment.validate_service(state, group, containment.MEMORY_MAX)
            containment.require(ready["invocation"] == state["InvocationID"]
                                and ready["identity"]["pid"] == int(state["MainPID"])
                                and containment.same_live(ready["identity"]), "Startup identity mismatch")
            containment.require(all(not Path(item["cgroup"]).is_relative_to(group) for item in protected.values()),
                                "Protected process entered compute group")
            recorded.update(containment.processes(group))
            containment.write_new(folder / "ADMISSION.json", {
                "invocation": state["InvocationID"], "service": state,
                "limits": containment.kernel_guard(group, containment.MEMORY_MAX),
            })
            with (folder / "telemetry.jsonl").open("x") as telemetry:
                while True:
                    state = containment.observe_service(telemetry, group, containment.MEMORY_MAX, ready["invocation"], 1)
                    containment.require(state["InvocationID"] == ready["invocation"], "Compute identity changed")
                    recorded.update(containment.processes(group))
                    containment.append_sample(telemetry, {"time": containment.now(), "service": state,
                                                         "counters": containment.counter_sample(group)})
                    if state.get("ActiveState") in {"failed", "inactive"} or state.get("SubState") == "exited":
                        break
                    containment.observe_live_limits(group, containment.MEMORY_MAX)
                    time.sleep(1)
            journals = containment.capture_journal(folder, request, ready["invocation"])
            containment.write_new(folder / "RESULT.json", {"service": state, "journals": journals})
        finally:
            containment.command(["systemctl", "--user", "stop", containment.UNIT], check=False)
            if group is not None:
                containment.wait_drain(group, recorded, 60)
            containment.unload_after_drain()
            containment.require(all(containment.same_live(item) for item in protected.values()), "Protected process disappeared")
            containment.write_new(folder / "DRAINED.json", {
                "all_descendants_drained": True, "protected_processes_survived": True, "processes": recorded,
            })
        success = state.get("Result") == "success" and state.get("ExecMainStatus") == "0"
        for filename in ["stdout.log", "stderr.log"]:
            lines = (folder / filename).read_text().splitlines()
            if success:
                print("\n".join(line for line in lines if any(marker in line for marker in
                    ["Build completed", "INTEGRATION_COMPLETE", "Artifacts:", ": PASS", ": FAIL", "depends on axioms"])), flush=True)
            else:
                errors = [index for index, line in enumerate(lines) if "error:" in line or "error(" in line]
                print("\n".join(lines[errors[0]:] if errors else lines[-80:]), flush=True)
        print(json.dumps({"success": success, "evidence": str(folder)}), flush=True)
        return 0 if success else 1


if __name__ == "__main__":
    if sys.argv[1:2] == ["_child"]:
        child(Path(sys.argv[2]))
    else:
        raise SystemExit(supervise(sys.argv[1:]))
