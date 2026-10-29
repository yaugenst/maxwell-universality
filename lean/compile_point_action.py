#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Sequential fresh kernel compilation of the complete point-witness action."""
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence/point_action_compile"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    EVIDENCE.mkdir(exist_ok=True)
    manifest_path = ROOT / "evidence/point_action_manifest.json"
    manifest = json.loads(manifest_path.read_text())
    for name, expected in manifest["table_sha256"].items():
        assert digest(ROOT / name) == expected
    receipt = {"started_utc": datetime.now(timezone.utc).isoformat(),
               "manifest_sha256": digest(manifest_path),
               "mode": "Sequential, nice 10, Lean -j1, warningAsError; kernel decide only",
               "memory_method": "GNU time maximum resident set size, KiB, maximum child process",
               "checks": [], "all_passed": False}
    for module in manifest["modules"]:
        name = module["module"]
        source = ROOT / f"Maxwell/Certificate/PointWitness/{name}.lean"
        output = ROOT / f".lake/build/lib/lean/Maxwell/Certificate/PointWitness/{name}.olean"
        assert digest(source) == module["source_sha256"]
        cap = "4500" if name == "ActionComplete" else "3500"
        command = ["nice", "-n10", "/usr/bin/time", "-v", "-o", str(EVIDENCE / f"{name}.time"),
                   "lake", "env", "lean", "-j1", f"-M{cap}",
                   "-DwarningAsError=true", "-o", str(output), str(source)]
        start = time.monotonic()
        with (EVIDENCE / f"{name}.log").open("w") as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        check = {"module": name, "command": command, "exit_code": result.returncode,
                 "elapsed_seconds": time.monotonic() - start, "source_sha256": digest(source)}
        if result.returncode == 0:
            check["olean_sha256"] = digest(output)
        receipt["checks"].append(check)
        (EVIDENCE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(f"{name}: exit {result.returncode}, {check['elapsed_seconds']:.2f}s", flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
    for name, expected in manifest["table_sha256"].items():
        assert digest(ROOT / name) == expected
    assert digest(manifest_path) == receipt["manifest_sha256"]
    audit = (EVIDENCE / "ActionComplete.log").read_text()
    assert audit.count("depends on axioms: [propext, Classical.choice, Quot.sound]") == 2
    receipt.update({"all_passed": True, "tables_unchanged": True,
                    "axioms": ["propext", "Classical.choice", "Quot.sound"],
                    "finished_utc": datetime.now(timezone.utc).isoformat()})
    (EVIDENCE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    main()
