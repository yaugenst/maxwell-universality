#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Audit the completed fresh corrector action run and its exact input bindings."""
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence"
RUN = EVIDENCE / "corrector_action_compile"
SOURCE = ROOT / "Maxwell/Certificate/CorrectorWitness"
OBJECT = ROOT / ".lake/build/lib/lean/Maxwell/Certificate/CorrectorWitness"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    receipt_path = RUN / "receipt.json"
    manifest_path = EVIDENCE / "corrector_action_manifest.json"
    witness_path = EVIDENCE / "corrector_witness_manifest.json"
    receipt = json.loads(receipt_path.read_text())
    manifest = json.loads(manifest_path.read_text())
    witness = json.loads(witness_path.read_text())
    assert receipt["all_passed"]
    assert digest(manifest_path) == receipt["manifest_sha256"]
    assert digest(witness_path) == receipt["witness_manifest_sha256"]
    expected = {f"{kind}{v}" for v in range(6) for kind in ["Numerator", "Imagenumerator"]}
    expected.update(f"Action{v}D{d}X{x:02d}" for v in range(6) for d in range(3) for x in range(20))
    expected.update(f"Action{v}Complete" for v in range(6))
    expected.add("ActionComplete")
    assert len(receipt["checks"]) == len(expected) == 379
    assert {c["module"] for c in receipt["checks"]} == expected
    input_hashes = {}
    for path, expected_hash in manifest["table_sha256"].items():
        assert digest(ROOT / path) == expected_hash
        input_hashes[path] = expected_hash
    for path, expected_hash in witness["canonical_sha256"].items():
        assert digest(Path(path)) == expected_hash
        input_hashes[path] = expected_hash
    for module in manifest["modules"]:
        assert digest(SOURCE / f"{module['module']}.lean") == module["source_sha256"]
    output_hashes, memory = {}, []
    for check in receipt["checks"]:
        name = check["module"]
        assert check["exit_code"] == 0
        source, output = SOURCE / f"{name}.lean", OBJECT / f"{name}.olean"
        assert digest(source) == check["source_sha256"]
        assert digest(output) == check["olean_sha256"]
        text = source.read_text()
        assert not re.search(r"\b(sorry|native_decide)\b|^\s*axiom\b", text, re.MULTILINE)
        for path in [source, output, RUN / f"{name}.log", RUN / f"{name}.time"]:
            output_hashes[str(path.relative_to(ROOT))] = digest(path)
        timing = (RUN / f"{name}.time").read_text()
        match = re.search(r"Maximum resident set size \(kbytes\): (\d+)", timing)
        assert match is not None
        memory.append((int(match[1]), name))
    audit = (RUN / "ActionComplete.log").read_text()
    expected_axioms = "depends on axioms: [propext, Classical.choice, Quot.sound]"
    assert audit.count(expected_axioms) == 6
    for v in range(6):
        assert f"Maxwell.Certificate.CorrectorWitness.numerator{v}_action" in audit
    peak, peak_module = max(memory)
    result = {
        "status": "PASS",
        "audited_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "All 36,000 actual integer Yee-action coordinates of six literal corrector columns at L++-.",
        "modules": len(expected), "checked_coordinates": 36000,
        "elapsed_seconds": receipt["elapsed_seconds"],
        "peak_rss_kib": peak, "peak_rss_module": peak_module,
        "memory_method": "GNU time maximum resident set size of one Lean child; two children maximum, aggregate peak not measured.",
        "axioms": ["propext", "Classical.choice", "Quot.sound"],
        "canonical_unchanged": True, "tables_unchanged": True,
        "manifest_sha256": digest(manifest_path),
        "witness_manifest_sha256": digest(witness_path),
        "receipt_sha256": digest(receipt_path),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "automation_current_sha256": {
            name: digest(ROOT / name) for name in [
                "generate_corrector_witness.py", "generate_point_action.py",
                "compile_corrector_action.py", "audit_corrector_action.py",
                "lean-toolchain", "lake-manifest.json",
            ]
        },
        "input_sha256": input_hashes,
        "output_sha256": output_hashes,
        "initial_failure": "Preserved in corrector_action_compile_initial_failure; a concurrent lake build briefly removed a dependency object. This full fresh retry uses direct lean -o commands.",
    }
    output = EVIDENCE / "corrector_action_postflight.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS: {len(expected)} modules, 36,000 coordinates, {receipt['elapsed_seconds']:.2f}s, peak child {peak} KiB ({peak_module}).")
    print(f"Postflight SHA256: {digest(output)}")


if __name__ == "__main__":
    main()
