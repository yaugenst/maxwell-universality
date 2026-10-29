#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Benchmark import-light FFT checks with exact existing-data bindings.

Only a new FFTRawWitness namespace is written. Existing stage proposals,
coefficient tables, semantic checks, and production manifests are unchanged.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence/fft_stage_proposals"
OUT = ROOT / "Maxwell/Certificate/FFTRawWitness"
RAW = "Maxwell.Certificate.FFTRawWitness"
OLD = "Maxwell.Certificate.FFTWitness"


def lit(a):
    return f"⟨{int(a[0])}, {int(a[1])}, {int(a[2])}⟩"


def lst(a):
    return "[" + ", ".join(a) + "]"


@lru_cache(None)
def archive_data(path):
    with np.load(path) as source:
        return {k: source[k] for k in source.files}


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--label", choices=["Lower", "Upper"], default="Lower")
    parser.add_argument("--direction", type=int, choices=range(3), default=0)
    parser.add_argument("--column", type=int, choices=range(28), default=12)
    parser.add_argument("--forward", action="store_true")
    parser.add_argument("--only-x", action="store_true", help="Generate only the optimized X stage and its binding")
    args = parser.parse_args(argv)
    OUT.mkdir(exist_ok=True)
    prefix = f"{args.label}{'Forward' if args.forward else ''}D{args.direction}C{args.column:02}"
    data = archive_data(EVIDENCE / f"{args.label.lower()}{'_forward' if args.forward else ''}.npz")
    coefs = json.loads((EVIDENCE / "coefficients.json").read_text())["normalized_root_tables"]
    mode = "forward" if args.forward else "inverse"

    def write(name, imports, body, analytic=False):
        s = "\n".join("import " + p for p in imports) + "\n"
        s += f"namespace {RAW}\nopen DyadicKernel\n"
        if analytic:
            s += "open FFTWitness FourierBinding Maxwell.Spectral.PrimitiveYee\nopen Matrix\n"
        s += "noncomputable section\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
        s += body + f"\nend\nend {RAW}\n"
        (OUT / f"{name}.lean").write_text(s)

    coeff_body = ""
    coeff_sound = ""
    for n in [10, 20]:
        k = coefs[str(n)]
        rows = [lst(lit([k[(20//n)*a*b%20][0], (1 if args.forward else -1)*k[(20//n)*a*b%20][1],
                          k[(20//n)*a*b%20][2]]) for b in range(n)) for a in range(n)]
        name = mode + str(n)
        kernel = f"kernel{n} a b" if args.forward else f"(kernel{n} b a).conjugate"
        coeff_body += f"def {name} : List (List Rectangle) := {lst(rows)}\n"
        coeff_sound += (f"theorem {name}_binding : {name} =\n"
                        f"    List.ofFn (fun a : Fin {n} => List.ofFn (fun b : Fin {n} =>\n"
                        f"      Rectangle.ofFFT ({kernel}))) := by\n  decide +kernel\n")
    constants = mode.title() + "Constants"
    write(constants, ["Maxwell.Certificate.DyadicRawFFT"], coeff_body)
    write(constants + "Sound", [RAW + "." + constants, "Maxwell.Certificate.DyadicRawFFTRows", OLD + ".Constants"], coeff_sound, True)
    modules = [RAW + "." + constants, RAW + "." + constants + "Sound"]
    modules += [OLD + "." + prefix + f for f in ["Input", "First", "Second", "Third", "Result", "Native", "NativeCheck", "CheckTBlocks"]]
    stages = ([('X', 'Input', 'First', 20, 0), ('Y', 'Second', 'Third', 10, 1), ('Z', 'Third', 'Result', 10, 2)]
              if args.forward else [('Z', 'Input', 'First', 10, 2), ('Y', 'First', 'Second', 10, 1), ('X', 'Third', 'Result', 20, 0)])
    if args.only_x:
        stages = [stage for stage in stages if stage[0] == 'X']
    for axis, before, after, n, ax in stages:
        outer = 10 if axis == 'X' else 20
        arrays = [data[f.lower()][:, args.direction, args.column, :].reshape(20, 10, 10, 3) for f in [before, after]]
        name = prefix + "Raw" + axis
        raw = ""
        sound = ""
        for a in range(outer):
            for b in range(10):
                ix = [a, b]
                ix.insert(ax, slice(None))
                line = f"{name}A{a:02}B{b:02}"
                for part, arr in zip(["Input", "Output"], arrays):
                    raw += f"def {line}{part} : List Rectangle := {lst(lit(v) for v in arr[tuple(ix)])}\n"
                raw += (f"theorem {line}_checked : lineCheck 52 {mode}{n}\n"
                        f"    {line}Input {line}Output = true := by\n  decide +kernel\n")
                point = [f"(j,{a},{b})", f"({a},j,{b})", f"({a},{b},j)"][ax]
                target = point.replace("j", "i")
                kernel = f"kernel{n} i j" if args.forward else f"(kernel{n} j i).conjugate"
                sound += (f"theorem {line}_accepted (i : Fin {n}) :\n"
                          f"    DyadicRectangle.dotCheck 52 52 (fun j : Fin {n} => {prefix}{before} {point})\n"
                          f"      (fun j => {kernel}) ({prefix}{after} {target}) = true := by\n"
                          f"  exact DyadicKernel.lineCheck_sound (p := 52) (q := 52) (fun j : Fin {n} => {prefix}{before} {point})\n"
                          f"    (fun i j => {kernel}) (fun j : Fin {n} => {prefix}{after} {point})\n"
                          f"    {line}Input {mode}{n} {line}Output\n"
                          f"    (by decide +kernel) {mode}{n}_binding (by decide +kernel) {line}_checked i\n")
        kernel = f"kernel{n}" if args.forward else f"(DyadicFFT.adjoint kernel{n})"
        sound += (f"theorem {name}_accepted : DyadicFFT.axis{axis}Check 52 52 {kernel}\n"
                  f"    {prefix}{before} {prefix}{after} = true := by\n"
                  f"  apply DyadicFFT.axis{axis}Check_of_rows\n  rintro ⟨x,y,z⟩\n")
        cases = {'X': 'y <;> fin_cases z', 'Y': 'x <;> fin_cases z', 'Z': 'x <;> fin_cases y'}[axis]
        variable = {'X': 'x', 'Y': 'y', 'Z': 'z'}[axis]
        sound += f"  fin_cases {cases}\n"
        sound += "\n".join(f"  · exact {name}A{a:02}B{b:02}_accepted {variable}" for a in range(outer) for b in range(10)) + "\n"
        write(name, [RAW + "." + constants], raw)
        write(name + "Sound", [RAW + "." + name, RAW + "." + constants + "Sound", OLD + "." + prefix + before,
                               OLD + "." + prefix + after], sound, True)
        modules += [RAW + "." + name, RAW + "." + name + "Sound"]

    if args.only_x:
        (EVIDENCE / f"{prefix}_raw_x_modules.json").write_text(json.dumps(modules, indent=2) + "\n")
        print(f"Generated raw X-stage and exact binding for {prefix}; production files unchanged.")
        return

    proposal = "Proposal"
    fields = ["First", "Second", "Third", "Result"]
    body = f"def {prefix}RawProposal : DyadicFFT.{proposal} := ⟨{', '.join(prefix+f for f in fields)}⟩\n"
    body += (f"theorem {prefix}_raw_accepted : DyadicFFT.{mode}Check 52 52 kernel20 kernel10 twiddle\n"
             f"    {prefix}Input {prefix}RawProposal = true := by\n"
             f"  apply DyadicFFT.{mode}Check_of_stages\n")
    order = ['X', 'T', 'Y', 'Z'] if args.forward else ['Z', 'Y', 'T', 'X']
    for axis in order:
        if axis != 'T':
            body += f"  · exact {prefix}Raw{axis}_accepted\n"
        else:
            body += "  · apply DyadicFFT.diagonalCheck_of_rows\n    rintro ⟨x,y,z⟩\n    fin_cases x\n"
            body += "\n".join(f"    · exact {prefix}CheckTX{x:02}_accepted y z" for x in range(20)) + "\n"
    transform = "((transform 0).conjTranspose *ᵥ v)" if args.forward else "(transform 0 *ᵥ v)"
    body += (f"theorem {prefix}_raw_{mode}_contains (v : Cell → ℂ)\n"
             f"    (hv : DyadicFFT.Contains 52 {prefix}Input v) :\n"
             f"    DyadicFFT.Contains 52 {prefix}Result {transform} :=\n"
             f"  checked_{mode} _ _ _ hv {prefix}_raw_accepted\n"
             f"theorem {prefix}_raw_native_{mode}_contains (v : Cell → ℂ)\n"
             f"    (hv : DyadicFFT.Contains 52 {prefix}Input v) :\n"
             f"    DyadicFFT.Contains 52 {prefix}Native {transform} := by\n"
             "  intro r\n  exact DyadicRectangle.subsetCheck_sound\n"
             f"    ({prefix}NativeCheck_accepted r.1 r.2.1 r.2.2)\n"
             f"    ({prefix}_raw_{mode}_contains v hv r)\n")
    write(prefix + "Complete", [RAW + "." + prefix + "Raw" + axis + "Sound" for axis in ['X', 'Y', 'Z']] +
          [OLD + "." + prefix + "NativeCheck", OLD + "." + prefix + "CheckTBlocks"], body, True)
    modules.append(RAW + "." + prefix + "Complete")
    (EVIDENCE / f"{prefix}_raw_modules.json").write_text(json.dumps(modules, indent=2) + "\n")
    print(f"Generated {len(modules)} prototype modules for {prefix}; production files unchanged.")


if __name__ == "__main__":
    main()
