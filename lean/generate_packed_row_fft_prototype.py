#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Stage one row-packed FFT benchmark without launching Lean."""
from hashlib import sha256
import json
from pathlib import Path

import numpy as np
from generate_packed_fft_prototype import packed, WIDTH, PREFIX

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "Maxwell/Certificate/GlobalFFTPackedRows"
EVIDENCE = ROOT / "evidence/global_fft_packed_rows"
NS = "Maxwell.Certificate.GlobalFFTPackedRows"


def array(xs):
    return "#[" + ", ".join(xs) + "]"


def field(values):
    values = values.reshape(20, 10, 10, 3)
    return array(array(packed(row) for row in block) for block in values)


def write(name, imports, body):
    source = "\n".join("import " + m for m in imports)
    source += f"\nnamespace {NS}\nopen DyadicKernel GlobalFFTComputed\n"
    source += "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
    source += body + f"\nend {NS}\n"
    path = OUT / (name + ".lean")
    path.write_text(source)
    return {"module": NS + "." + name, "source_bytes": path.stat().st_size,
            "sha256": sha256(path.read_bytes()).hexdigest()}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    path = ROOT / "evidence/global_center_proposals/record0000.npz"
    metadata = json.loads(path.with_suffix(".json").read_text())
    assert sha256(path.read_bytes()).hexdigest() == metadata["output_sha256"]
    with np.load(path) as src:
        input_values = np.array(src["curl"][:, 0, 0], dtype=object) * 16
        native_values = np.array(src["inverse"][:, 0, 0], dtype=object) * 16
    prefix = PREFIX
    body = (f"noncomputable def {prefix}Input : PackedRowsFFT.Field := {field(input_values)}\n"
            f"noncomputable def {prefix}Native : PackedRowsFFT.Field := {field(native_values)}\n"
            f"noncomputable def {prefix}First : Option PackedRowsFFT.Field :=\n"
            f"  PackedRowsFFT.axisZ {WIDTH} 52 (FFT.adjoint kernel10) {prefix}Input\n"
            f"noncomputable def {prefix}Computed : Option PackedRowsFFT.Field :=\n"
            f"  PackedRowsFFT.inverse {WIDTH} 52 kernel20 kernel10 twiddle {prefix}Input\n")
    records = [write(prefix + "Data", ["Maxwell.Certificate.DyadicPackedRowsFFT",
                                       "Maxwell.Certificate.GlobalFFTComputed.Constants"], body)]
    checks = {
        "First": f"{prefix}First.isSome",
        "Point": f"{prefix}Computed.any (fun n => subsetCheck (PackedRowsFFT.get {WIDTH} n 0 0 0) (PackedRowsFFT.get {WIDTH} {prefix}Native 0 0 0))",
        "Row": f"{prefix}Computed.any (fun n => PackedRowsFFT.subsetRow {WIDTH} n {prefix}Native 0)",
        "Full": f"{prefix}Computed.any (fun n => PackedRowsFFT.subset {WIDTH} n {prefix}Native)",
    }
    for name, predicate in checks.items():
        records.append(write(prefix + "Check" + name, [NS + "." + prefix + "Data"],
            f"theorem {prefix}_{name.lower()} :\n    {predicate} = true := by decide +kernel\n"))
    (EVIDENCE / "staged.json").write_text(json.dumps({
        "canonical_sha256": metadata["output_sha256"], "width": WIDTH,
        "input_key": "curl", "native_key": "inverse", "direction": 0, "column": 0,
        "status": "staged, no numerical acceptance yet", "modules": records,
    }, indent=2) + "\n")
    print(json.dumps(records, indent=2))


if __name__ == "__main__":
    main()
