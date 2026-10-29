#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Check the actual full quadratic residual and its exact Gram with one worker."""
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "Maxwell/Certificate/QuadraticWitness"
OBJECT = ROOT / ".lake/build/lib/lean/Maxwell/Certificate/QuadraticWitness"
EVIDENCE = ROOT / "evidence/quadratic_witness_compile"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    EVIDENCE.mkdir(exist_ok=True)
    OBJECT.mkdir(parents=True, exist_ok=True)
    manifest_paths = [ROOT / f"evidence/quadratic_{kind}_manifest.json" for kind in ["witness", "gram"]]
    manifests = [json.loads(p.read_text()) for p in manifest_paths]
    manifest_hashes = {str(p.relative_to(ROOT)): digest(p) for p in manifest_paths}
    assert digest(manifest_paths[0]) == manifests[1]["action_manifest_sha256"]
    inputs = dict(manifests[0]["input_sha256"])
    frozen = ROOT.parent / "certificates/yee/results/defects/inversion_feshbach_curvature_acceptance.json"
    inputs[str(frozen)] = manifests[1]["canonical_frozen_sha256"]
    for path, expected in inputs.items():
        assert digest(Path(path)) == expected
    modules = {m["module"]: m for manifest in manifests for m in manifest["modules"]}
    for name, m in modules.items():
        assert digest(SOURCE / f"{name}.lean") == m["source_sha256"]
    old_path = EVIDENCE / "receipt.json"
    old = json.loads(old_path.read_text()) if old_path.exists() else {"checks": []}
    reusable = {c["module"]: c for c in old["checks"] if c["exit_code"] == 0 and
                digest(SOURCE / f"{c['module']}.lean") == c["source_sha256"] and
                (OBJECT / f"{c['module']}.olean").exists() and
                digest(OBJECT / f"{c['module']}.olean") == c["olean_sha256"]}
    receipt = {"started_utc": datetime.now(timezone.utc).isoformat(), "all_passed": False,
               "manifest_sha256": manifest_hashes, "mode": "One nice10 single-threaded Lean worker; -M4500 actions, -M3500 dots, -M5000 final imports.",
               "reused_modules": sorted(reusable), "checks": []}
    start = time.monotonic()

    def check(name, cap=4500):
        if name in reusable:
            result = reusable[name]
        else:
            source, output = SOURCE / f"{name}.lean", OBJECT / f"{name}.olean"
            source_hash = digest(source)
            command = ["nice", "-n10", "/usr/bin/time", "-v", "-o", str(EVIDENCE / f"{name}.time"),
                       "lake", "env", "lean", "-j1", f"-M{cap}",
                       "-DwarningAsError=true", "-o", str(output), str(source)]
            started = time.monotonic()
            with (EVIDENCE / f"{name}.log").open("w") as log:
                proc = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
            assert digest(source) == source_hash
            result = {"module": name, "command": command, "exit_code": proc.returncode,
                      "elapsed_seconds": time.monotonic() - started, "source_sha256": source_hash}
            if proc.returncode == 0:
                result["olean_sha256"] = digest(output)
        receipt["checks"].append(result)
        (EVIDENCE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(f"{name}: exit {result['exit_code']}, {result['elapsed_seconds']:.2f}s", flush=True)
        if result["exit_code"]:
            raise SystemExit(result["exit_code"])

    # Publish stable literal tables and matrix positivity proofs first.
    for name, m in modules.items():
        if m["kind"] == "table":
            check(name, 3500)
    check("Data", 5000)
    check("GramData", 3500)
    check("GramNorm", 4500)
    check("GramRelative", 4500)
    for name, m in modules.items():
        if m["kind"] in {"action_chunk", "action_complete", "audit"}:
            check(name, 5000 if m["kind"] == "audit" else 4500)
    for name, m in modules.items():
        if m["kind"] == "dot":
            check(name, 3500)
    check("Gram", 5000)
    check("Complete", 5000)
    assert {c["module"] for c in receipt["checks"]} == set(modules)
    assert len(receipt["checks"]) == len(modules)
    for path, expected in inputs.items():
        assert digest(Path(path)) == expected
    for path, expected in manifest_hashes.items():
        assert digest(ROOT / path) == expected
    audit = (EVIDENCE / "ActionComplete.log").read_text()
    assert audit.count("depends on axioms: [propext, Classical.choice, Quot.sound]") == 12
    final_audit = (EVIDENCE / "Complete.log").read_text()
    assert final_audit.count("depends on axioms: [propext, Classical.choice, Quot.sound]") == 3
    memory, output_hashes = [], {}
    for c in receipt["checks"]:
        name = c["module"]
        source, output = SOURCE / f"{name}.lean", OBJECT / f"{name}.olean"
        assert digest(source) == c["source_sha256"]
        assert digest(output) == c["olean_sha256"]
        assert not re.search(r"\b(sorry|native_decide)\b|^\s*axiom\b", source.read_text(), re.MULTILINE)
        for path in [source, output, EVIDENCE / f"{name}.log", EVIDENCE / f"{name}.time"]:
            output_hashes[str(path.relative_to(ROOT))] = digest(path)
        timing = (EVIDENCE / f"{name}.time").read_text()
        memory.append((int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", timing)[1]), name))
    receipt.update({"all_passed": True, "inputs_unchanged": True,
                    "elapsed_seconds": time.monotonic() - start,
                    "finished_utc": datetime.now(timezone.utc).isoformat(),
                    "axioms": ["propext", "Classical.choice", "Quot.sound"]})
    receipt_path = EVIDENCE / "receipt.json"
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    peak, peak_name = max(memory)
    result = {"status": "PASS", "scope": "12 actual full-quadratic residual vectors, full stacked Gram, exact norm and relative-Hessian PSD bounds.",
              "checked_action_coordinates": 72000, "dot_products": manifests[1]["dot_products"],
              "modules": len(modules), "elapsed_seconds": receipt["elapsed_seconds"],
              "peak_rss_kib": peak, "peak_rss_module": peak_name,
              "memory_method": "GNU time maximum resident set of the single Lean child.",
              "inputs_unchanged": True, "input_sha256": inputs,
              "manifest_sha256": manifest_hashes, "receipt_sha256": digest(receipt_path),
              "output_sha256": output_hashes, "axioms": receipt["axioms"]}
    (ROOT / "evidence/quadratic_witness_postflight.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS: {len(modules)} modules; peak child {peak} KiB; elapsed {receipt['elapsed_seconds']:.2f}s.", flush=True)


if __name__ == "__main__":
    main()
