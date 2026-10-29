# /// script
# requires-python = ">=3.12"
# ///
"""Strict direct compiler replay for the finite RealRAM simulator leaves."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent
PREFIX = "Maxwell.Cost.RealSimulation."
SOURCES = {
    PREFIX + p.stem: p
    for p in (ROOT / "Maxwell/Cost/RealSimulation").glob("*.lean")
}
SOURCES["Maxwell.Cost.RealSimulation"] = ROOT / "Maxwell/Cost/RealSimulation.lean"
parser = argparse.ArgumentParser()
parser.add_argument("--output", default="evidence/real_simulation_complete")
args = parser.parse_args()
OUT = ROOT / args.output
OUT.mkdir(parents=True, exist_ok=True)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


order: list[str] = []
seen: set[str] = set()


def visit(module: str) -> None:
    if module in seen:
        return
    seen.add(module)
    for dep in re.findall(r"^import\s+(\S+)", SOURCES[module].read_text(), re.M):
        if dep in SOURCES:
            visit(dep)
    order.append(module)


for module in sorted(SOURCES):
    visit(module)

tracked = list(SOURCES.values()) + [ROOT / "Maxwell/Cost/Machine.lean", ROOT / "Maxwell/Cost/RealLink.lean"]
preflight = {str(path.relative_to(ROOT)): digest(path) for path in tracked}
(OUT / "input_hashes.json").write_text(json.dumps(preflight, indent=2) + "\n")
records = []
for module in order:
    source = SOURCES[module]
    name = source.stem
    obj = ROOT / ".lake/build/lib/lean" / Path(*module.split(".")).with_suffix(".olean")
    command = [
        "nice", "-n", "10", "/usr/bin/time", "-v",
        "lake", "env", "lean", "-j1", "-M4500",
        "-DwarningAsError=true", "-o", str(obj), str(source),
    ]
    start = time.monotonic()
    with (OUT / f"{name}.log").open("w") as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    record = {
        "module": module, "command": command, "returncode": result.returncode,
        "elapsed_seconds": time.monotonic() - start,
        "source_sha256": digest(source),
        "object_sha256": digest(obj) if result.returncode == 0 else None,
    }
    records.append(record)
    (OUT / "receipt.json").write_text(json.dumps(records, indent=2) + "\n")
    print(f"{name}: {'PASS' if result.returncode == 0 else 'FAIL'}", flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)

postflight = {str(path.relative_to(ROOT)): digest(path) for path in tracked}
assert preflight == postflight, "A simulator source or shared machine dependency changed during replay"
(OUT / "postflight.json").write_text(json.dumps({
    "all_passed": True, "module_count": len(records), "sources_unchanged": True,
    "input_hashes": postflight,
    "object_hashes": {record["module"]: record["object_sha256"] for record in records},
}, indent=2) + "\n")
