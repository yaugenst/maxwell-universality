#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Stage a bounded computed-FFT benchmark; never starts numerical Lean work."""
import argparse
from hashlib import sha256
import json
from pathlib import Path

import numpy as np
import generate_fft_stage_proposals as arithmetic
from generate_forward_fft_proposals import forward_stages

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "Maxwell/Certificate/GlobalFFTComputed"
EVIDENCE = ROOT / "evidence/global_fft_computed"
NS = "Maxwell.Certificate.GlobalFFTComputed"


def array(xs):
    return "#[" + ", ".join(xs) + "]"


def field(xs):
    return array(array(array(arithmetic.literal(v) for v in row) for row in block) for block in xs)


def write(name, imports, body, sound=False):
    source = "\n".join("import " + m for m in imports) + f"\nnamespace {NS}\n"
    source += "open DyadicKernel\n"
    if sound:
        source += "open FourierBinding Maxwell.Spectral.PrimitiveYee Matrix\n"
    source += "noncomputable section\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
    source += body + f"\nend\nend {NS}\n"
    (OUT / (name + ".lean")).write_text(source)


def round_floor(pairs):
    values = [arithmetic.mul_exact(a, b) for a, b in pairs]
    r, i, e = (sum(v[j] for v in values) for j in range(3))
    return (r // arithmetic.S, i // arithmetic.S, e // arithmetic.S + 2)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--forward", action="store_true")
    parser.add_argument("--direction", type=int, choices=range(3), default=0)
    parser.add_argument("--column", type=int, choices=range(30), default=0)
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    path = ROOT / "evidence/global_center_proposals/record0000.npz"
    info = json.loads(path.with_suffix(".json").read_text())
    assert sha256(path.read_bytes()).hexdigest() == info["output_sha256"]
    co = json.loads((ROOT / "evidence/fft_stage_proposals/coefficients.json").read_text())
    body = "def roots : Array Rectangle := " + array(map(arithmetic.literal, co["roots"])) + "\n"
    for n in [10, 20]:
        body += f"def coefficients{n} : Array Rectangle := " + array(map(arithmetic.literal, co["normalized_root_tables"][str(n)])) + "\n"
        body += (f"def kernel{n} : FFT.Kernel {n} := fun i j =>\n"
                 f"  (coefficients{n}[({20//n}*i.val*j.val)%20]?).getD zero\n")
    body += ("def twiddle : FFT.Field := FFT.build fun x y z =>\n"
             "  (roots[(x.val*(y.val+z.val))%20]?).getD zero\n")
    write("Constants", ["Maxwell.Certificate.DyadicKernelFFT"], body)
    sound = ""
    for n in [10, 20]:
        sound += (f"theorem kernel{n}_binding : FFT.toKernel kernel{n} = FFTWitness.kernel{n} := by\n"
                  "  funext i j\n  fin_cases i <;> revert j <;> decide +kernel\n\n")
    sound += ("theorem twiddle_binding : FFT.toField twiddle = FFTWitness.twiddle := by\n"
              "  funext r\n  rcases r with ⟨x,y,z⟩\n  simp only [FFT.toField, twiddle, FFT.get_build]\n"
              "  fin_cases x <;> fin_cases y <;> revert z <;> decide +kernel\n\n")
    for mode in ["inverse", "forward"]:
        transform = "(transform 0 *ᵥ v)" if mode == "inverse" else "((transform 0).conjTranspose *ᵥ v)"
        sound += (f"theorem {mode}_contains (input : FFT.Field) (v : Cell → ℂ)\n"
                  "    (hv : DyadicFFT.Contains 52 (FFT.toField input) v) :\n"
                  f"    DyadicFFT.Contains 52 (FFT.toField (FFT.{mode} 52 kernel20 kernel10 twiddle input))\n"
                  f"      {transform} := by\n"
                  f"  exact FFT.{mode}_contains kernel20 kernel10 twiddle input\n"
                  "    (by simpa only [kernel20_binding] using FFTWitness.kernel20_contains)\n"
                  "    (by simpa only [kernel10_binding] using FFTWitness.kernel10_contains)\n"
                  "    (by simpa only [twiddle_binding] using FFTWitness.twiddle_contains) v hv\n\n")
    write("ConstantsSound", [NS + ".Constants", "Maxwell.Certificate.DyadicKernelFFTSound",
                             "Maxwell.Certificate.FFTWitness.Constants"], sound, True)
    mode = "Forward" if args.forward else "Inverse"
    prefix = f"Record0000Central{mode}D{args.direction}C{args.column:02}"
    with np.load(path) as source:
        akey, bkey = ("spatial", "weighted") if args.forward else ("curl", "inverse")
        a = np.array(source[akey][:, args.direction, args.column], dtype=object).reshape(20,10,10,3)*16
        b = np.array(source[bkey][:, args.direction, args.column], dtype=object).reshape(20,10,10,3)*16
    # This changes only this process's proposal arithmetic. No source modules or
    # stored coefficient tables are modified.
    arithmetic.round_dot = round_floor
    kernels = {int(n): v for n, v in co["normalized_root_tables"].items()}
    stages = forward_stages(a, co["roots"], kernels) if args.forward else arithmetic.inverse_stages(a, co["roots"], kernels)
    r = stages[-1]
    slack = np.minimum(b[...,2]-np.abs(r[...,0]-b[...,0])-r[...,2],
                       b[...,2]-np.abs(r[...,1]-b[...,1])-r[...,2])
    assert int(slack.min()) >= 0, int(slack.min())
    body = (f"def {prefix}Input : FFT.Field := {field(a)}\n"
            f"def {prefix}Native : FFT.Field := {field(b)}\n"
            f"def {prefix}Computed : FFT.Field := FFT.{mode.lower()} 52 kernel20 kernel10 twiddle {prefix}Input\n")
    write(prefix + "Data", [NS + ".Constants"], body)
    write(prefix + "CheckPoint", [NS + "." + prefix + "Data"],
          f"theorem {prefix}_point : subsetCheck (FFT.get {prefix}Computed 0 0 0)\n"
          f"    (FFT.get {prefix}Native 0 0 0) = true := by decide +kernel\n")
    write(prefix + "CheckRow", [NS + "." + prefix + "Data"],
          f"theorem {prefix}_row : FFT.subsetRow {prefix}Computed {prefix}Native 0 = true := by decide +kernel\n")
    body = "".join(f"theorem {prefix}_row{x:02} : FFT.subsetRow {prefix}Computed {prefix}Native {x} = true := by decide +kernel\n" for x in range(20))
    write(prefix + "CheckFull", [NS + "." + prefix + "Data"], body)
    transform = "(transform 0 *ᵥ v)" if not args.forward else "((transform 0).conjTranspose *ᵥ v)"
    body = (f"theorem {prefix}_native_contains (v : Cell → ℂ)\n"
            f"    (hv : DyadicFFT.Contains 52 (FFT.toField {prefix}Input) v) :\n"
            f"    DyadicFFT.Contains 52 (FFT.toField {prefix}Native) {transform} := by\n"
            f"  have h := {mode.lower()}_contains {prefix}Input v hv\n"
            "  rintro ⟨x,y,z⟩\n"
            f"  apply FFT.subsetRow_sound (a := {prefix}Computed) (y := y) (z := z) _ (h (x,y,z))\n"
            "  fin_cases x\n")
    body += "".join(f"  · exact {prefix}_row{x:02}\n" for x in range(20))
    write(prefix + "Complete", [NS + ".ConstantsSound", NS + "." + prefix + "CheckFull"], body, True)
    modules = [NS + "." + x for x in ["Constants", "ConstantsSound", prefix + "Data", prefix + "CheckPoint", prefix + "CheckRow", prefix + "CheckFull", prefix + "Complete"]]
    (EVIDENCE / (prefix + "_modules.json")).write_text(json.dumps(modules, indent=2)+"\n")
    (EVIDENCE / (prefix + ".json")).write_text(json.dumps({"canonical_sha256": info["output_sha256"],
        "input_key": akey, "native_key": bkey, "direction": args.direction, "column": args.column,
        "native_min_slack": int(slack.min()), "status": "Untrusted input proposal; Lean computed checks pending",
        "modules": modules}, indent=2)+"\n")
    print(prefix, "diagnostic slack", int(slack.min()), "no proof worker started")


if __name__ == "__main__":
    main()
