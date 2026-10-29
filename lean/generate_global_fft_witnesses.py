#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Propose canonical global-record FFT checks without invoking a proof worker.

Native p48 rectangles are lifted exactly to p52, including their radii. The
integer stages are proposals only. Generated Lean theorems check their
arithmetic and bind every stage to the actual FCC Fourier transform.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path

import numpy as np

from generate_fft_stage_proposals import field_literal, inverse_stages, literal
from generate_forward_fft_proposals import forward_stages

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "Maxwell/Certificate/GlobalFFTWitness"
EVIDENCE = ROOT / "evidence/global_fft_proposals"
NS = "Maxwell.Certificate.GlobalFFTWitness"
OLD = "Maxwell.Certificate.FFTWitness"
RAW = "Maxwell.Certificate.FFTRawWitness"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def list_literal(values):
    return "[" + ", ".join(values) + "]"


def vector_literal(values):
    return "![" + ", ".join(values) + "]"


class Writer:
    def __init__(self, prefix, forward, arrays):
        self.prefix, self.forward, self.arrays = prefix, forward, arrays
        self.mode = "forward" if forward else "inverse"
        self.modules = []

    def write(self, suffix, imports, body, raw=False):
        name = self.prefix + suffix
        source = "\n".join("import " + m for m in imports) + "\n\n"
        source += f"namespace {NS}\n"
        source += "open DyadicKernel\n" if raw else (
            "open FFTWitness FourierBinding Maxwell.Spectral.PrimitiveYee Matrix\n")
        source += "noncomputable section\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n"
        source += body + f"\nend\nend {NS}\n"
        (OUT / (name + ".lean")).write_text(source)
        self.modules.append(NS + "." + name)

    def dep(self, suffix):
        return NS + "." + self.prefix + suffix

    def fields(self):
        for stage, values in self.arrays.items():
            name = self.prefix + stage
            self.write(stage, [OLD + ".ConstantsData"],
                f"def {name}Data : Fin 20 → Fin 10 → Fin 10 → DyadicRectangle :=\n"
                f"  {field_literal(values)}\n\n"
                f"def {name} : DyadicFFT.Field := fun p => {name}Data p.1 p.2.1 p.2.2\n")
        p = self.prefix
        self.write("NativeCheck", [self.dep("Result"), self.dep("Native")],
            f"theorem {p}NativeCheck_accepted (x : Fin 20) (y z : Fin 10) :\n"
            f"    DyadicRectangle.subsetCheck ({p}Result (x,y,z))\n"
            f"      ({p}Native (x,y,z)) = true := by\n"
            "  fin_cases x <;> revert y z <;> decide +kernel\n")

    def raw_x(self):
        p = self.prefix
        before, after = ("Input", "First") if self.forward else ("Third", "Result")
        coeff = self.mode + "20"
        raw, sound = "", ""
        for y in range(10):
            for z in range(10):
                name = f"{p}RawXA{y:02}B{z:02}"
                for part, stage in [("Input", before), ("Output", after)]:
                    data = list_literal(literal(v) for v in self.arrays[stage][:,y,z])
                    raw += f"def {name}{part} : List Rectangle := {data}\n"
                raw += (f"theorem {name}_checked : lineCheck 52 FFTRawWitness.{coeff}\n"
                        f"    {name}Input {name}Output = true := by\n  decide +kernel\n")
                kernel = "kernel20 i j" if self.forward else "(kernel20 j i).conjugate"
                sound += (
                    f"theorem {name}_accepted (i : Fin 20) :\n"
                    f"    DyadicRectangle.dotCheck 52 52 (fun j : Fin 20 => {p}{before} (j,{y},{z}))\n"
                    f"      (fun j => {kernel}) ({p}{after} (i,{y},{z})) = true := by\n"
                    f"  exact DyadicKernel.lineCheck_sound (p := 52) (q := 52)\n"
                    f"    (fun j : Fin 20 => {p}{before} (j,{y},{z}))\n"
                    f"    (fun i j => {kernel}) (fun j : Fin 20 => {p}{after} (j,{y},{z}))\n"
                    f"    {name}Input FFTRawWitness.{coeff} {name}Output\n"
                    f"    (by decide +kernel) FFTRawWitness.{coeff}_binding\n"
                    f"    (by decide +kernel) {name}_checked i\n")
        kernel = "kernel20" if self.forward else "(DyadicFFT.adjoint kernel20)"
        sound += (f"theorem {p}RawX_accepted : DyadicFFT.axisXCheck 52 52 {kernel}\n"
                  f"    {p}{before} {p}{after} = true := by\n"
                  "  apply DyadicFFT.axisXCheck_of_rows\n  rintro ⟨x,y,z⟩\n"
                  "  fin_cases y <;> fin_cases z\n")
        sound += "".join(f"  · exact {p}RawXA{y:02}B{z:02}_accepted x\n"
                         for y in range(10) for z in range(10))
        constant = RAW + "." + self.mode.title() + "Constants"
        self.write("RawX", [constant], raw, raw=True)
        self.write("RawXSound", [self.dep("RawX"), constant + "Sound",
                                 self.dep(before), self.dep(after)], sound)

    def list_axis(self, axis):
        p = self.prefix
        before, after = (("Second", "Third") if axis == "Y" else ("Third", "Result")) \
            if self.forward else (("First", "Second") if axis == "Y" else ("Input", "First"))
        data = self.arrays[before]
        table = vector_literal(vector_literal(
            list_literal(literal(v) for v in (data[a,:,b] if axis == "Y" else data[a,b,:]))
            for b in range(10)) for a in range(20))
        point = "(a,j,b)" if axis == "Y" else "(a,b,j)"
        inp = p + "ListInput" + axis
        constants = "ForwardListConstants" if self.forward else "ListConstants"
        coeff = "forwardCoefficients10" if self.forward else "inverseCoefficients10"
        self.write("ListInput" + axis, [self.dep(before), OLD + "." + constants],
            f"def {inp} : Fin 20 → Fin 10 → List DyadicRectangle :=\n  {table}\n\n"
            f"theorem {inp}_binding (a : Fin 20) (b : Fin 10) :\n"
            f"    {inp} a b = List.ofFn (fun j : Fin 10 => {p}{before} {point}) := by\n"
            "  revert a b\n  decide +kernel\n")
        body = ""
        for x in range(20):
            args, row, src = (f"{x} z", "y", f"({x},j,z)") if axis == "Y" \
                else (f"{x} y", "z", f"({x},y,j)")
            name = f"{p}ListCheck{axis}X{x:02}"
            kernel = f"kernel10 {row} j" if self.forward else f"(kernel10 j {row}).conjugate"
            body += (
                f"theorem {name}_literal (y z : Fin 10) :\n"
                f"    DyadicRectangle.listDotCheck 52 52\n"
                f"      (({inp} {args}).zip ({coeff} {row}))\n"
                f"      ({p}{after} ({x},y,z)) = true := by\n"
                "  revert y z\n  decide +kernel\n\n"
                f"theorem {name}_accepted (y z : Fin 10) :\n"
                f"    DyadicRectangle.dotCheck 52 52 (fun j : Fin 10 => {p}{before} {src})\n"
                f"      (fun j => {kernel}) ({p}{after} ({x},y,z)) = true :=\n"
                f"  DyadicRectangle.dotCheck_of_zip ({inp}_binding {args})\n"
                f"    ({coeff}_binding {row}) ({name}_literal y z)\n\n")
        self.write("ListCheck" + axis + "Blocks", [self.dep("ListInput" + axis), self.dep(after)], body)

    def twiddle(self):
        p = self.prefix
        before, after = ("First", "Second") if self.forward else ("Second", "Third")
        body = ""
        for x in range(20):
            t = f"twiddle ({x},y,z)" if self.forward else f"(twiddle ({x},y,z)).conjugate"
            body += (
                f"theorem {p}CheckTX{x:02}_accepted (y z : Fin 10) :\n"
                f"    DyadicRectangle.rescaleCheck 52 52\n"
                f"      (DyadicRectangle.mulExact ({p}{before} ({x},y,z)) ({t}))\n"
                f"      ({p}{after} ({x},y,z)) = true := by\n"
                "  revert y z\n  decide +kernel\n\n")
        self.write("CheckTBlocks", [self.dep(before), self.dep(after)], body)

    def complete(self):
        p = self.prefix
        body = (f"def {p}Proposal : DyadicFFT.Proposal :=\n"
                f"  ⟨{p}First,{p}Second,{p}Third,{p}Result⟩\n\n"
                f"theorem {p}_accepted : DyadicFFT.{self.mode}Check 52 52 kernel20 kernel10 twiddle\n"
                f"    {p}Input {p}Proposal = true := by\n"
                f"  apply DyadicFFT.{self.mode}Check_of_stages\n")
        for axis in (["X", "T", "Y", "Z"] if self.forward else ["Z", "Y", "T", "X"]):
            if axis == "X":
                body += f"  · exact {p}RawX_accepted\n"
                continue
            lemma = "diagonalCheck_of_rows" if axis == "T" else f"axis{axis}Check_of_rows"
            name = "CheckT" if axis == "T" else "ListCheck" + axis
            body += f"  · apply DyadicFFT.{lemma}\n    rintro ⟨x,y,z⟩\n    fin_cases x\n"
            body += "".join(f"    · exact {p}{name}X{x:02}_accepted y z\n" for x in range(20))
        transform = "((transform 0).conjTranspose *ᵥ v)" if self.forward else "(transform 0 *ᵥ v)"
        body += (
            f"\ntheorem {p}_{self.mode}_contains (v : Cell → ℂ)\n"
            f"    (hv : DyadicFFT.Contains 52 {p}Input v) :\n"
            f"    DyadicFFT.Contains 52 {p}Result {transform} :=\n"
            f"  checked_{self.mode} _ _ _ hv {p}_accepted\n\n"
            f"theorem {p}_native_{self.mode}_contains (v : Cell → ℂ)\n"
            f"    (hv : DyadicFFT.Contains 52 {p}Input v) :\n"
            f"    DyadicFFT.Contains 52 {p}Native {transform} := by\n"
            "  intro r\n  exact DyadicRectangle.subsetCheck_sound\n"
            f"    ({p}NativeCheck_accepted r.1 r.2.1 r.2.2)\n"
            f"    ({p}_{self.mode}_contains v hv r)\n")
        self.write("Complete", [self.dep(s) for s in
            ["RawXSound", "ListCheckYBlocks", "ListCheckZBlocks", "CheckTBlocks", "NativeCheck"]], body)

    def emit(self):
        self.fields()
        self.raw_x()
        for axis in ["Y", "Z"]:
            self.list_axis(axis)
        self.twiddle()
        self.complete()
        return self.modules


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--record", type=int, default=0)
    parser.add_argument("--family", choices=["central", "derivative", "gradient", "all"], default="central")
    parser.add_argument("--columns", type=int, help="Restrict to the first columns for a bounded prototype")
    parser.add_argument("--direction", type=int, choices=range(3), help="Restrict to one component")
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    source = ROOT / f"evidence/global_center_proposals/record{args.record:04}.npz"
    metadata = source.with_suffix(".json")
    info = json.loads(metadata.read_text())
    assert info["precision"] == 48
    assert info["output_sha256"] == digest(source), "Canonical proposal archive changed"
    coefficients = ROOT / "evidence/fft_stage_proposals/coefficients.json"
    co = json.loads(coefficients.read_text())
    assert co["precision"] == 52
    roots, kernels = co["roots"], {int(n): k for n, k in co["normalized_root_tables"].items()}
    families = [("Central", "", 30)] if args.family in ("central", "all") else []
    if args.family in ("derivative", "all"):
        families += [(f"Axis{a}Derivative", f"axis{a}_", 30) for a in range(3)]
    if args.family in ("gradient", "all"):
        families += [(f"Axis{a}Gradient", f"axis{a}_gradient_", 15) for a in range(3)]
    modules, diagnostics = [], []
    with np.load(source) as archive:
        for family, stem, count in families:
            for forward in [False, True]:
                mode = "Forward" if forward else "Inverse"
                input_key, output_key = (stem + "spatial", stem + "weighted") if forward \
                    else (stem + "curl", stem + "inverse")
                inputs, native = archive[input_key], archive[output_key]
                assert inputs.shape == native.shape == (2000, 3, count, 3)
                for column in range(min(args.columns or count, count)):
                    for direction in ([args.direction] if args.direction is not None else range(3)):
                        prefix = f"Record{args.record:04}{family}{mode}D{direction}C{column:02}"
                        a = np.asarray(inputs[:,direction,column,:], dtype=object).reshape(20,10,10,3) * 16
                        target = np.asarray(native[:,direction,column,:], dtype=object).reshape(20,10,10,3) * 16
                        stages = forward_stages(a, roots, kernels) if forward else inverse_stages(a, roots, kernels)
                        arrays = dict(zip(["Input", "First", "Second", "Third", "Result", "Native"],
                                          (a, *stages, target), strict=True))
                        result = stages[-1]
                        slack = np.minimum(target[...,2] - np.abs(result[...,0]-target[...,0]) - result[...,2],
                                           target[...,2] - np.abs(result[...,1]-target[...,1]) - result[...,2])
                        if int(slack.min()) < 0:
                            raise ValueError(f"{prefix}: native inclusion diagnostic failed, minimum slack {slack.min()}")
                        generated = Writer(prefix, forward, arrays).emit()
                        modules.extend(generated)
                        diagnostics.append({"prefix": prefix, "input_key": input_key, "output_key": output_key,
                            "direction": direction, "column": column, "included": 2000,
                            "min_slack": int(slack.min()), "max_proposed_radius": int(result[...,2].max())})
                    print(f"Proposed record{args.record:04} {family} {mode} column{column:02}", flush=True)
    tag = f"record{args.record:04}_{args.family}"
    if args.columns is not None:
        tag += f"_first{args.columns}"
    if args.direction is not None:
        tag += f"_d{args.direction}"
    (EVIDENCE / (tag + "_modules.json")).write_text(json.dumps(modules, indent=2) + "\n")
    report = {"record": args.record, "source": str(source.relative_to(ROOT)), "source_sha256": digest(source),
        "source_metadata_sha256": digest(metadata), "coefficient_sha256": digest(coefficients),
        "source_precision": 48, "target_precision": 52, "lift_factor_all_three_channels": 16,
        "status": "Untrusted proposals; generated Lean checks have not been run by this generator.",
        "module_count": len(modules), "scalar_transforms": len(diagnostics), "diagnostics": diagnostics}
    (EVIDENCE / (tag + ".json")).write_text(json.dumps(report, indent=2) + "\n")
    print(f"Staged {len(diagnostics)} transforms and {len(modules)} modules; no proof worker started.")


if __name__ == "__main__":
    main()
