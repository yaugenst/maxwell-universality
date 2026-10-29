# /// script
# requires-python = ">=3.12"
# ///
"""Bind the strict simulator replay and axiom audit to current project sources."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "evidence/real_simulation_complete_v2"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


records = json.loads((OUT / "receipt.json").read_text())
assert len(records) == 39 and all(r["returncode"] == 0 for r in records)
for record in records:
    source = ROOT / Path(*record["module"].split(".")).with_suffix(".lean")
    artifact = ROOT / ".lake/build/lib/lean" / Path(*record["module"].split(".")).with_suffix(".olean")
    assert digest(source) == record["source_sha256"], source
    assert digest(artifact) == record["object_sha256"], artifact

axioms = (OUT / "axioms.log").read_text()
reports = re.findall(r"depends on axioms: \[([^]]*)\]", axioms)
assert len(reports) == 9
standard = {"propext", "Classical.choice", "Quot.sound"}
assert all(set(report.split(", ")) <= standard for report in reports)

closure = {}


def visit(module: str) -> None:
    if module in closure or not module.startswith("Maxwell."):
        return
    source = ROOT / Path(*module.split(".")).with_suffix(".lean")
    artifact = ROOT / ".lake/build/lib/lean" / Path(*module.split(".")).with_suffix(".olean")
    closure[module] = {"source_sha256": digest(source), "object_sha256": digest(artifact)}
    for dep in re.findall(r"^import\s+(\S+)", source.read_text(), re.M):
        visit(dep)


visit("Maxwell.Cost.RealSimulation")
audit = {
    "all_replayed_modules_unchanged": True,
    "replayed_modules": len(records),
    "axiom_audited_theorems": len(reports),
    "only_standard_axioms": True,
    "receipt_sha256": digest(OUT / "receipt.json"),
    "axioms_sha256": digest(OUT / "axioms.log"),
    "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
    "lake_manifest_sha256": digest(ROOT / "lake-manifest.json"),
    "project_import_closure": closure,
    "scope": "Actual finite simulation and every-target-state word bound. Source PrefixAddressBound remains an explicit premise; E/D instantiation is separate.",
}
path = OUT / "audit.json"
path.write_text(json.dumps(audit, indent=2) + "\n")
print(json.dumps({"project_modules": len(closure), "audit_sha256": digest(path)}, indent=2))
