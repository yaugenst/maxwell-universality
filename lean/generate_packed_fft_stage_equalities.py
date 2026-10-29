#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""One bounded exact-equality checkpoint experiment, not a production generator.

Stage literals are untrusted proposals. Lean must prove every stage equals the
deterministic evaluator, then prove the final rectangle inclusion.
"""
import json
from pathlib import Path

import numpy as np
import generate_fft_stage_proposals as arithmetic
from generate_packed_row_fft_prototype import write, field, NS, EVIDENCE, PREFIX
from generate_deterministic_fft_prototype import round_floor

ROOT = Path(__file__).resolve().parent


def main():
    co = json.loads((ROOT / "evidence/fft_stage_proposals/coefficients.json").read_text())
    with np.load(ROOT / "evidence/global_center_proposals/record0000.npz") as source:
        a = np.array(source["curl"][:, 0, 0], dtype=object).reshape(20, 10, 10, 3)*16
    arithmetic.round_dot = round_floor
    kernels = {int(n): v for n, v in co["normalized_root_tables"].items()}
    stages = arithmetic.inverse_stages(a, co["roots"], kernels)
    names = [PREFIX + "Stage" + str(i) for i in range(1, 5)]
    body = ""
    for name, value in zip(names, stages):
        body += f"noncomputable def {name} : PackedRowsFFT.Field := {field(value)}\n"
    inputs = [PREFIX + "Input", *names[:3]]
    operators = ["PackedRowsFFT.Forced.axisZ 64 52 (FFT.adjoint kernel10)",
                 "PackedRowsFFT.Forced.axisY 64 52 (FFT.adjoint kernel10)",
                 "PackedRowsFFT.Forced.diagonal 64 52 (FFT.conjugateField twiddle)",
                 "PackedRowsFFT.Forced.axisX 64 52 (FFT.adjoint kernel20)"]
    for i, (name, op, input_name) in enumerate(zip(names, operators, inputs), 1):
        body += (f"theorem {PREFIX}_stage{i}_exact :\n"
                 f"    {op} {input_name} = some {name} := by decide +kernel\n")
    body += (f"theorem {PREFIX}_final_subset :\n"
             f"    PackedRowsFFT.subset 64 {names[-1]} {PREFIX}Native = true := by decide +kernel\n")
    body += (f"theorem {PREFIX}_checkpointed_full :\n"
             f"    (PackedRowsFFT.Forced.inverse 64 52 kernel20 kernel10 twiddle {PREFIX}Input).any\n"
             f"      (fun a => PackedRowsFFT.subset 64 a {PREFIX}Native) = true := by\n"
             "  exact PackedRowsFFT.inverse_accept_of_stages 64 52 kernel20 kernel10 twiddle\n"
             f"    {PREFIX}Input {names[0]} {names[1]} {names[2]} {names[3]} {PREFIX}Native\n"
             + " ".join(PREFIX + f"_stage{i}_exact" for i in range(1, 5))
             + f" {PREFIX}_final_subset\n")
    record = write(PREFIX + "CheckStageEqualities", [NS + "." + PREFIX + "Data",
        "Maxwell.Certificate.DyadicPackedRowsCompose"], body)
    (EVIDENCE / "stage_equalities_staged.json").write_text(json.dumps({
        "status": "One bounded proposed exact-equality checkpoint experiment, Lean acceptance pending",
        "module": record, "stored_stage_arrays": 4,
        "scope": "Every proposed intermediate must equal deterministic arithmetic from the previous checked input. No stage equality is an assumption."}, indent=2)+"\n")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
