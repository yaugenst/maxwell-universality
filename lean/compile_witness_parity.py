#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Check all eight frozen-vector parities with two bounded Lean processes."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence/witness_parity_compile"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def check_module(namespace, name, cap=3500):
    relative = Path(f"Maxwell/Certificate/{namespace}/{name}")
    source = ROOT / relative.with_suffix(".lean")
    output = ROOT / ".lake/build/lib/lean" / relative.with_suffix(".olean")
    key = f"{namespace}_{name}"
    command = ["nice", "-n10", "/usr/bin/time", "-v", "-o", str(EVIDENCE / f"{key}.time"),
               "lake", "env", "lean", "-j1", f"-M{cap}",
               "-DwarningAsError=true", "-o", str(output), str(source)]
    source_hash = digest(source)
    start = time.monotonic()
    with (EVIDENCE / f"{key}.log").open("w") as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    assert digest(source) == source_hash
    check = {"namespace": namespace, "module": name, "command": command,
             "exit_code": result.returncode, "elapsed_seconds": time.monotonic() - start,
             "source_sha256": source_hash}
    if result.returncode == 0:
        check["olean_sha256"] = digest(output)
    return check


def main():
    EVIDENCE.mkdir(exist_ok=True)
    manifest_path = ROOT / "evidence/witness_parity_manifest.json"
    manifest = json.loads(manifest_path.read_text())
    operator = ROOT / "Maxwell/Certificate/InversionInteger.lean"
    operator_hash = digest(operator)
    for path, expected in manifest["table_sha256"].items():
        assert digest(ROOT / path) == expected
    for module in manifest["modules"]:
        path = ROOT / f"Maxwell/Certificate/{module['namespace']}/{module['module']}.lean"
        assert digest(path) == module["source_sha256"]
    receipt = {"started_utc": datetime.now(timezone.utc).isoformat(), "all_passed": False,
               "manifest_sha256": digest(manifest_path), "operator_source_sha256": operator_hash,
               "mode": "Two nice10 Lean children maximum, each -j1 -M3500; final imports -M5000.",
               "checks": []}
    start = time.monotonic()
    used_axioms = set()

    def record(check):
        receipt["checks"].append(check)
        (EVIDENCE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(f"{check['namespace']}.{check['module']}: exit {check['exit_code']}, {check['elapsed_seconds']:.2f}s", flush=True)

    for namespace, columns in [("PointWitness", 2), ("CorrectorWitness", 6)]:
        for v in range(columns):
            with ThreadPoolExecutor(max_workers=2) as pool:
                futures = [pool.submit(check_module, namespace, f"Parity{v}X{x:02d}") for x in range(20)]
                for future in as_completed(futures):
                    check = future.result()
                    record(check)
                    if check["exit_code"]:
                        for pending in futures:
                            pending.cancel()
                        raise SystemExit(check["exit_code"])
            check = check_module(namespace, f"Parity{v}Complete")
            record(check)
            if check["exit_code"]:
                raise SystemExit(check["exit_code"])
        check = check_module(namespace, "ParityComplete", cap=5000)
        record(check)
        if check["exit_code"]:
            raise SystemExit(check["exit_code"])
        audit = (EVIDENCE / f"{namespace}_ParityComplete.log").read_text()
        for v in range(columns):
            theorem = f"Maxwell.Certificate.{namespace}.numerator{v}_parity"
            match = re.search(re.escape(f"'{theorem}' depends on axioms: [") + r"([^]]*)\]", audit)
            if match:
                axioms = {name.strip() for name in match[1].split(",") if name.strip()}
            else:
                assert f"'{theorem}' does not depend on any axioms" in audit
                axioms = set()
            assert axioms <= {"propext", "Classical.choice", "Quot.sound"}
            used_axioms.update(axioms)
    assert len(receipt["checks"]) == len(manifest["modules"]) == 170
    assert digest(operator) == operator_hash
    assert digest(manifest_path) == receipt["manifest_sha256"]
    for path, expected in manifest["table_sha256"].items():
        assert digest(ROOT / path) == expected
    output_hashes, memory = {}, []
    for check in receipt["checks"]:
        namespace, name = check["namespace"], check["module"]
        source = ROOT / f"Maxwell/Certificate/{namespace}/{name}.lean"
        output = ROOT / f".lake/build/lib/lean/Maxwell/Certificate/{namespace}/{name}.olean"
        assert digest(source) == check["source_sha256"]
        assert digest(output) == check["olean_sha256"]
        key = f"{namespace}_{name}"
        for path in [source, output, EVIDENCE / f"{key}.log", EVIDENCE / f"{key}.time"]:
            output_hashes[str(path.relative_to(ROOT))] = digest(path)
        timing = (EVIDENCE / f"{key}.time").read_text()
        memory.append((int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", timing)[1]), key))
    receipt.update({"all_passed": True, "tables_unchanged": True,
                    "operator_source_unchanged": True,
                    "axioms": sorted(used_axioms),
                    "elapsed_seconds": time.monotonic() - start,
                    "finished_utc": datetime.now(timezone.utc).isoformat()})
    receipt_path = EVIDENCE / "receipt.json"
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    peak, peak_module = max(memory)
    postflight = {"status": "PASS", "scope": manifest["scope"], "checked_coordinates": 48000,
                  "modules": 170, "elapsed_seconds": receipt["elapsed_seconds"],
                  "peak_rss_kib": peak, "peak_rss_module": peak_module,
                  "memory_method": "GNU time peak of one Lean child; aggregate of two children not measured.",
                  "table_sha256": manifest["table_sha256"], "tables_unchanged": True,
                  "operator_source_sha256": operator_hash, "manifest_sha256": digest(manifest_path),
                  "receipt_sha256": digest(receipt_path), "axioms": receipt["axioms"],
                  "output_sha256": output_hashes}
    (ROOT / "evidence/witness_parity_postflight.json").write_text(json.dumps(postflight, indent=2) + "\n")
    print(f"PASS: all 48,000 coordinates, {receipt['elapsed_seconds']:.2f}s, peak child {peak} KiB.", flush=True)


if __name__ == "__main__":
    main()
