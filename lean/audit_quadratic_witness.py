#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Recheck final quadratic-witness artifacts and all canonical input hashes."""
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    postflight_path = ROOT / "evidence/quadratic_witness_postflight.json"
    receipt_path = ROOT / "evidence/quadratic_witness_compile/receipt.json"
    postflight = json.loads(postflight_path.read_text())
    receipt = json.loads(receipt_path.read_text())
    assert postflight["status"] == "PASS" and receipt["all_passed"]
    assert digest(receipt_path) == postflight["receipt_sha256"]
    for relative, expected in postflight["manifest_sha256"].items():
        assert digest(ROOT / relative) == expected
    gram_manifest = json.loads((ROOT / "evidence/quadratic_gram_manifest.json").read_text())
    frozen = ROOT.parent / "certificates/yee/results/defects/inversion_feshbach_curvature_acceptance.json"
    # This is the additional input of the Gram generator, beyond action inputs.
    postflight["input_sha256"][str(frozen)] = gram_manifest["canonical_frozen_sha256"]
    for path, expected in postflight["input_sha256"].items():
        assert digest(Path(path)) == expected
    for relative, expected in postflight["output_sha256"].items():
        path = ROOT / relative
        assert digest(path) == expected
        if path.suffix == ".lean":
            assert not re.search(r"\b(sorry|native_decide)\b|^\s*axiom\b", path.read_text(), re.MULTILINE)
    evidence = ROOT / "evidence/quadratic_witness_compile"
    for name, count in [("ActionComplete", 12), ("Complete", 3)]:
        log = (evidence / f"{name}.log").read_text()
        assert log.count("depends on axioms: [propext, Classical.choice, Quot.sound]") == count
    source = ROOT / "Maxwell/Certificate/QuadraticWitness/VerifiedAssembly.lean"
    output = ROOT / ".lake/build/lib/lean/Maxwell/Certificate/QuadraticWitness/VerifiedAssembly.olean"
    source_hash = digest(source)
    audit_source = evidence / "AssemblyAudit.lean"
    audit_source.write_text("import Maxwell.Certificate.QuadraticWitness.VerifiedAssembly\n\n"
                            "#print axioms Maxwell.Certificate.QuadraticWitness.numerators_action\n"
                            "#print axioms Maxwell.Certificate.QuadraticWitness.savedQuadraticResidual_eq\n")
    checks = []
    for name, checked_source, extra in [
        ("VerifiedAssembly", source, ["-o", str(output)]),
        ("AssemblyAudit", audit_source, []),
    ]:
        log_path, time_path = evidence / f"{name}.log", evidence / f"{name}.time"
        command = ["nice", "-n10", "/usr/bin/time", "-v", "-o", str(time_path),
                   "lake", "env", "lean", "-j1", "-M4500",
                   "-DwarningAsError=true", *extra, str(checked_source)]
        started = time.monotonic()
        with log_path.open("w") as log:
            proc = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        assert proc.returncode == 0, f"{name} failed; see {log_path}"
        peak = int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", time_path.read_text())[1])
        checks.append({"module": name, "command": command, "exit_code": proc.returncode,
                       "elapsed_seconds": time.monotonic() - started, "peak_rss_kib": peak})
        for path in [checked_source, log_path, time_path]:
            postflight["output_sha256"][str(path.relative_to(ROOT))] = digest(path)
    assert digest(source) == source_hash
    assembly_axioms = re.findall(r"depends on axioms:\s*\[([^\]]*)\]",
                                (evidence / "AssemblyAudit.log").read_text())
    assert len(assembly_axioms) == 2
    assert all([axiom.strip() for axiom in group.split(",")] ==
               ["propext", "Classical.choice", "Quot.sound"] for group in assembly_axioms)
    postflight["output_sha256"][str(output.relative_to(ROOT))] = digest(output)
    postflight["operator_assembly"] = {
        "status": "PASS", "source_sha256": source_hash, "checks": checks,
        "theorem": "Maxwell.Certificate.QuadraticWitness.savedQuadraticResidual_eq",
        "scope": "Unconditional actual saved residual equals the contraction of the checked twelve tensor columns.",
        "axioms": ["propext", "Classical.choice", "Quot.sound"],
    }
    postflight["final_audit"] = {
        "status": "PASS",
        "finished_utc": datetime.now(timezone.utc).isoformat(),
        "script_sha256": digest(Path(__file__)),
        "canonical_inputs": len(postflight["input_sha256"]),
        "outputs_rechecked": len(postflight["output_sha256"]),
        "canonical_frozen_hessian_unchanged": True,
    }
    postflight_path.write_text(json.dumps(postflight, indent=2) + "\n")
    print(f"PASS: {postflight['modules']} modules; {len(postflight['output_sha256'])} artifact hashes; "
          f"{len(postflight['input_sha256'])} canonical and saved-vector inputs.")
    print(f"postflight_sha256={digest(postflight_path)}")


if __name__ == "__main__":
    main()
