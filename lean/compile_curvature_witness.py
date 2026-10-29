#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Compile the actual curvature dot bindings and rounding estimate."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "Maxwell/Certificate/CurvatureWitness"
OBJECT = ROOT / ".lake/build/lib/lean/Maxwell/Certificate/CurvatureWitness"
EVIDENCE = ROOT / "evidence/curvature_witness_compile"


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
    manifest_path = ROOT / "evidence/curvature_witness_manifest.json"
    manifest = json.loads(manifest_path.read_text())
    old_path = EVIDENCE / "receipt.json"
    old = json.loads(old_path.read_text()) if old_path.exists() else {"checks": []}
    for path, expected in manifest["input_sha256"].items():
        assert digest(Path(path)) == expected
    for module in manifest["modules"]:
        assert digest(SOURCE / f"{module['module']}.lean") == module["source_sha256"]
    reusable = {check["module"]: check for check in old["checks"]
                if check["exit_code"] == 0 and
                digest(SOURCE / f"{check['module']}.lean") == check["source_sha256"] and
                (OBJECT / f"{check['module']}.olean").exists() and
                digest(OBJECT / f"{check['module']}.olean") == check["olean_sha256"]}
    receipt = {"started_utc": datetime.now(timezone.utc).isoformat(), "all_passed": False,
               "manifest_sha256": digest(manifest_path), "checks": [],
               "reused_modules": sorted(reusable),
               "mode": "One nice10 Lean -j1 process; D-dot chunks capped at4500MiB, B/Y dots3500MiB, binding imports5000MiB."}
    start = time.monotonic()

    def record(check):
        receipt["checks"].append(check)
        (EVIDENCE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(f"{check['module']}: exit {check['exit_code']}, {check['elapsed_seconds']:.2f}s", flush=True)

    def batch(names, cap=3500):
        pending_names = []
        for name in names:
            if name in reusable:
                record(reusable[name])
            else:
                pending_names.append(name)
        with ThreadPoolExecutor(max_workers=1) as pool:
            futures = [pool.submit(check_module, name, cap) for name in pending_names]
            for future in as_completed(futures):
                check = future.result()
                record(check)
                if check["exit_code"]:
                    for pending in futures:
                        pending.cancel()
                    raise SystemExit(check["exit_code"])

    batch(["Defs", "Factored", "Data"])
    batch([m["module"] for m in manifest["modules"] if m["kind"] == "dot_data"])
    batch([m["module"] for m in manifest["modules"] if m["kind"] == "dot_chunk"], cap=4500)
    batch([m["module"] for m in manifest["modules"] if m["module"].startswith("DotBY")])
    batch([m["module"] for m in manifest["modules"]
           if m["kind"] == "dot" and m["module"].startswith("DotD")])
    batch(["Rounding", "Bindings"], cap=5000)
    batch(["Complete"], cap=5000)
    assert len(receipt["checks"]) == len(manifest["modules"]) + 3 == 162
    for path, expected in manifest["input_sha256"].items():
        assert digest(Path(path)) == expected
    assert digest(manifest_path) == receipt["manifest_sha256"]
    audit = (EVIDENCE / "Complete.log").read_text()
    assert audit.count("depends on axioms: [propext, Classical.choice, Quot.sound]") == 2
    output_hashes, memory = {}, []
    for check in receipt["checks"]:
        name = check["module"]
        source, output = SOURCE / f"{name}.lean", OBJECT / f"{name}.olean"
        assert digest(source) == check["source_sha256"]
        assert digest(output) == check["olean_sha256"]
        for path in [source, output, EVIDENCE / f"{name}.log", EVIDENCE / f"{name}.time"]:
            output_hashes[str(path.relative_to(ROOT))] = digest(path)
        timing = (EVIDENCE / f"{name}.time").read_text()
        memory.append((int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", timing)[1]), name))
    receipt.update({"all_passed": True, "inputs_unchanged": True,
                    "axioms": ["propext", "Classical.choice", "Quot.sound"],
                    "elapsed_seconds": time.monotonic() - start,
                    "finished_utc": datetime.now(timezone.utc).isoformat()})
    receipt_path = EVIDENCE / "receipt.json"
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    peak, peak_module = max(memory)
    postflight = {"status": "PASS", "scope": "Actual frozen-vector Hessian coefficient binding and 1e-11 entry rounding error at L++-.",
                  "modules": 162, "dot_products": 60, "total_dot_summands": 360000,
                  "elapsed_seconds": receipt["elapsed_seconds"],
                  "peak_rss_kib": peak, "peak_rss_module": peak_module,
                  "memory_method": "GNU time maximum resident set of one checked Lean child; aggregate host memory not measured.",
                  "inputs_unchanged": True, "input_sha256": manifest["input_sha256"],
                  "manifest_sha256": digest(manifest_path), "receipt_sha256": digest(receipt_path),
                  "output_sha256": output_hashes, "axioms": receipt["axioms"]}
    (ROOT / "evidence/curvature_witness_postflight.json").write_text(json.dumps(postflight, indent=2) + "\n")
    print(f"PASS: 60 exact 6,000-coordinate dot products, {receipt['elapsed_seconds']:.2f}s, peak child {peak} KiB.", flush=True)


if __name__ == "__main__":
    main()
