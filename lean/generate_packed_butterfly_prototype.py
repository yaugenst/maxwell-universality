#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Stage one mixed-radix packed-row FFT measurement, with exact diagnostics."""
import json
from pathlib import Path

import numpy as np
import generate_fft_stage_proposals as arithmetic
from generate_packed_row_fft_prototype import write, NS, OUT, EVIDENCE, PREFIX

ROOT = Path(__file__).resolve().parent
S = 2**52


def dot(pairs):
    products = [arithmetic.mul_exact(a, b) for a, b in pairs]
    return tuple(sum(x[i] for x in products) // S + (2 if i == 2 else 0) for i in range(3))


def main():
    co = json.loads((ROOT / "evidence/fft_stage_proposals/coefficients.json").read_text())
    roots = co["roots"]
    norms = co["normalizations"]

    def five(a, stride):
        return [dot((a[j], roots[(stride*k*j) % 20]) for j in range(5)) for k in range(5)]

    def combine(ev, od, stride):
        n = len(ev)
        return [dot([(ev[k%n], (S, 0, 0)),
                     ((-od[k%n][0], -od[k%n][1], od[k%n][2]) if k >= n else od[k%n],
                      roots[(stride*(k%n)) % 20])]) for k in range(n*2)]

    def ten(a, sign):
        return combine(five(a[::2], 4*sign), five(a[1::2], 4*sign), 2*sign)

    def twenty(a, sign):
        return combine(ten(a[::2], sign), ten(a[1::2], sign), sign)

    def transform(a, sign):
        n = len(a)
        output = ten(a, sign) if n == 10 else twenty(a, sign)
        return [dot([(b, norms[str(n)])]) for b in output]

    def axis(a, which):
        out = np.empty_like(a)
        if which == 0:
            for y in range(10):
                for z in range(10):
                    out[:, y, z] = transform(a[:, y, z].tolist(), 1)
        elif which == 1:
            for x in range(20):
                for z in range(10):
                    out[x, :, z] = transform(a[x, :, z].tolist(), 1)
        else:
            for x in range(20):
                for y in range(10):
                    out[x, y, :] = transform(a[x, y, :].tolist(), 1)
        return out

    with np.load(ROOT / "evidence/global_center_proposals/record0000.npz") as source:
        a = np.array(source["curl"][:, 0, 0], dtype=object).reshape(20, 10, 10, 3)*16
        native = np.array(source["inverse"][:, 0, 0], dtype=object).reshape(20, 10, 10, 3)*16
    first = axis(a, 2)
    second = axis(first, 1)
    third = np.empty_like(second)
    for x in range(20):
        for y in range(10):
            for z in range(10):
                root = roots[(x*(y+z)) % 20]
                third[x, y, z] = dot([(second[x, y, z], (root[0], -root[1], root[2]))])
    final = axis(third, 0)
    slack = np.minimum(native[..., 2]-np.abs(final[..., 0]-native[..., 0])-final[..., 2],
                       native[..., 2]-np.abs(final[..., 1]-native[..., 1])-final[..., 2])
    assert int(slack.min()) >= 0, int(slack.min())
    body = ("noncomputable def root (m : Int) : Rectangle :=\n"
            "  (roots[(m % 20).toNat]?).getD zero\n")
    for n in [10, 20]:
        body += f"noncomputable def norm{n} : Rectangle := {arithmetic.literal(norms[str(n)])}\n"
    records = [write("ButterflyConstants", ["Maxwell.Certificate.GlobalFFTComputed.Constants",
                      "Maxwell.Certificate.DyadicPackedRowsButterfly"], body)]
    for kind, expression in [
            ("ButterflyFirst", f"(PackedRowsButterfly.axisZ 64 root norm10 1 {PREFIX}Input).isSome"),
            ("ButterflyFull", f"(PackedRowsButterfly.inverse 64 root norm20 norm10 twiddle {PREFIX}Input).any (fun a => PackedRowsFFT.subset 64 a {PREFIX}Native)")]:
        records.append(write(PREFIX + "Check" + kind, [NS + ".ButterflyConstants", NS + "." + PREFIX + "Data"],
            f"theorem {PREFIX}_{kind} :\n    {expression} = true := by decide +kernel\n"))
    (EVIDENCE / "butterfly_staged.json").write_text(json.dumps({
        "minimum_native_slack": int(slack.min()),
        "diagnostic_scope": "Exact integer proposal diagnostic only; Lean numerical checks pending",
        "modules": records,
    }, indent=2) + "\n")
    print("Mixed-radix integer diagnostic native minimum slack:", int(slack.min()))


if __name__ == "__main__":
    main()
