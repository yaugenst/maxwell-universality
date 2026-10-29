#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Sequential Lean kernel checks for the frozen cover, with fresh receipts."""
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence/cover_compile"
LEAN = "lake"


def main():
    EVIDENCE.mkdir(exist_ok=True)
    manifest_path = ROOT / "evidence/cover_data_manifest.json"
    manifest = json.loads(manifest_path.read_text())
    chunks = sorted(manifest["chunks"], key=lambda c: -c["source_bytes"])
    modules = [f"CoverDataCube{c['name']}" for c in chunks] + ["CoverDataComplete", "CoverDataAudit"]
    canonical = Path(manifest["canonical_proposal"])
    assert sha256(canonical.read_bytes()).hexdigest() == manifest["canonical_proposal_sha256"]
    receipt = {"started_utc": datetime.now(timezone.utc).isoformat(),
               "manifest_sha256": sha256(manifest_path.read_bytes()).hexdigest(),
               "mode": "Sequential, nice 10, Lean -j1, warningAsError; kernel decide only",
               "memory_method": "GNU time maximum resident set size, KiB, maximum child process",
               "checks": []}
    for name in modules:
        source = ROOT / f"Maxwell/Certificate/{name}.lean"
        output = ROOT / f".lake/build/lib/lean/Maxwell/Certificate/{name}.olean"
        command = ["nice", "-n10", "/usr/bin/time", "-v", "-o", str(EVIDENCE / f"{name}.time"),
                   LEAN, "env", "lean", "-j1", "-DwarningAsError=true", "-o", str(output), str(source)]
        start = time.monotonic()
        with (EVIDENCE / f"{name}.log").open("w") as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        check = {"module": name, "command": command, "exit_code": result.returncode,
                 "elapsed_seconds": time.monotonic() - start,
                 "source_sha256": sha256(source.read_bytes()).hexdigest()}
        if result.returncode == 0:
            check["olean_sha256"] = sha256(output.read_bytes()).hexdigest()
        receipt["checks"].append(check)
        receipt["all_passed"] = len(receipt["checks"]) == len(modules) and result.returncode == 0
        (EVIDENCE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(f"{name}: exit {result.returncode}, {check['elapsed_seconds']:.2f}s", flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
    receipt["canonical_postflight_sha256"] = sha256(canonical.read_bytes()).hexdigest()
    assert receipt["canonical_postflight_sha256"] == manifest["canonical_proposal_sha256"]
    assert sha256(manifest_path.read_bytes()).hexdigest() == receipt["manifest_sha256"]
    receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
    (EVIDENCE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    main()
