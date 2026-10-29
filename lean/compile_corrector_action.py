#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Compile six actual corrector actions with two bounded Lean processes."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence/corrector_action_compile"
SOURCE = ROOT / "Maxwell/Certificate/CorrectorWitness"
OBJECT = ROOT / ".lake/build/lib/lean/Maxwell/Certificate/CorrectorWitness"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def check_module(name, cap=3500):
    source, output = SOURCE / f"{name}.lean", OBJECT / f"{name}.olean"
    source_hash = digest(source)
    command = ["nice", "-n10", "/usr/bin/time", "-v", "-o", str(EVIDENCE / f"{name}.time"),
               "lake", "env", "lean", "-j1", f"-M{cap}",
               "-DwarningAsError=true", "-o", str(output), str(source)]
    start = time.monotonic()
    with (EVIDENCE / f"{name}.log").open("w") as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    assert digest(source) == source_hash
    check = {"module": name, "command": command, "exit_code": result.returncode,
             "elapsed_seconds": time.monotonic() - start, "source_sha256": source_hash}
    if result.returncode == 0:
        check["olean_sha256"] = digest(output)
    return check


def main():
    EVIDENCE.mkdir(exist_ok=True)
    OBJECT.mkdir(parents=True, exist_ok=True)
    manifest_path = ROOT / "evidence/corrector_action_manifest.json"
    witness_path = ROOT / "evidence/corrector_witness_manifest.json"
    manifest, witness = json.loads(manifest_path.read_text()), json.loads(witness_path.read_text())
    for name, expected in manifest["table_sha256"].items():
        assert digest(ROOT / name) == expected
    for module in manifest["modules"]:
        assert digest(SOURCE / f"{module['module']}.lean") == module["source_sha256"]
    receipt = {"started_utc": datetime.now(timezone.utc).isoformat(),
               "manifest_sha256": digest(manifest_path), "witness_manifest_sha256": digest(witness_path),
               "mode": "Two nice10 Lean processes maximum, each -j1, memory cap3500MiB; final import cap6000MiB",
               "memory_method": "GNU time maximum resident set size, KiB, maximum child process",
               "checks": [], "all_passed": False}
    start = time.monotonic()

    def record(check):
        receipt["checks"].append(check)
        (EVIDENCE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(f"{check['module']}: exit {check['exit_code']}, {check['elapsed_seconds']:.2f}s", flush=True)

    def batch(names):
        with ThreadPoolExecutor(max_workers=2) as pool:
            futures = [pool.submit(check_module, name) for name in names]
            for future in as_completed(futures):
                check = future.result()
                record(check)
                if check["exit_code"]:
                    for pending in futures:
                        pending.cancel()
                    raise SystemExit(check["exit_code"])

    # Literal tables are compiled first so independent Gram/residual proofs
    # can import all six columns while the action verification continues.
    batch([f"{kind}{v}" for v in range(6) for kind in ["Numerator", "Imagenumerator"]])
    for v in range(6):
        batch([f"Action{v}D{d}X{x:02d}" for d in range(3) for x in range(20)])
        check = check_module(f"Action{v}Complete")
        record(check)
        if check["exit_code"]:
            raise SystemExit(check["exit_code"])
    check = check_module("ActionComplete", cap=6000)
    record(check)
    if check["exit_code"]:
        raise SystemExit(check["exit_code"])
    for name, expected in manifest["table_sha256"].items():
        assert digest(ROOT / name) == expected
    for name, expected in witness["canonical_sha256"].items():
        assert digest(Path(name)) == expected
    for module in manifest["modules"]:
        assert digest(SOURCE / f"{module['module']}.lean") == module["source_sha256"]
    assert digest(manifest_path) == receipt["manifest_sha256"]
    assert digest(witness_path) == receipt["witness_manifest_sha256"]
    audit = (EVIDENCE / "ActionComplete.log").read_text()
    assert audit.count("depends on axioms: [propext, Classical.choice, Quot.sound]") == 6
    receipt.update({"all_passed": True, "tables_unchanged": True, "canonical_unchanged": True,
                    "axioms": ["propext", "Classical.choice", "Quot.sound"],
                    "elapsed_seconds": time.monotonic() - start,
                    "finished_utc": datetime.now(timezone.utc).isoformat()})
    (EVIDENCE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    main()
