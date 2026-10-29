#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Propose exact-integer FCC FFT stages and Lean kernel-check modules.

Decimal arithmetic only proposes coefficients. The roots, normalizations, and
all stage outputs require the generated Lean checks; Python acceptance is not
a proof. Source NPZ files are read without changing them.
"""
from __future__ import annotations
import argparse
from decimal import Decimal, localcontext
from hashlib import sha256
import json
import importlib.util
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'Maxwell/Certificate/FFTWitness'
EVIDENCE = ROOT / 'evidence/fft_stage_proposals'
S = 1 << 52


def root_proposals():
    with localcontext() as ctx:
        ctx.prec = 90
        pi = Decimal('3.141592653589793238462643383279502884197169399375105820974944592307816406286208998628')
        roots = []
        for i in range(20):
            x = 2*pi*Decimal(i)/20
            c = ct = Decimal(1)
            s = st = x
            for k in range(1, 100):
                ct *= -x*x/Decimal((2*k-1)*(2*k))
                st *= -x*x/Decimal((2*k)*(2*k+1))
                c += ct
                s += st
            roots.append((int((c*S).to_integral_value()), int((s*S).to_integral_value()), 1))
        norms = {n: (int((Decimal(S)/Decimal(n).sqrt()).to_integral_value()), 0, 1)
                 for n in (10, 20)}
    return roots, norms


def conjugate(a):
    return (int(a[0]), -int(a[1]), int(a[2]))


def mul_exact(a, b):
    ar, ai, ae = map(int, a)
    br, bi, be = map(int, b)
    return (ar*br-ai*bi, ar*bi+ai*br,
            (abs(ar)+abs(ai))*be+(abs(br)+abs(bi))*ae+2*ae*be)


def round_dot(pairs):
    values = [mul_exact(a, b) for a, b in pairs]
    re, im, error = (sum(v[i] for v in values) for i in range(3))
    cr, ci = (re+S//2)//S, (im+S//2)//S
    radius = (max(abs(re-cr*S), abs(im-ci*S))+error+S-1)//S
    return (cr, ci, radius)


def literal(a):
    return f'⟨{int(a[0])}, {int(a[1])}, {int(a[2])}⟩'


def vector(a):
    return '![' + ', '.join(literal(x) for x in a) + ']'


def coefficients():
    roots, norms = root_proposals()
    kernels = {n: [round_dot([(norms[n], conjugate(a))]) for a in roots] for n in (10, 20)}
    OUT.mkdir(parents=True, exist_ok=True)
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    tables = '''import Maxwell.Certificate.DyadicFFT
import Maxwell.Certificate.FFTConstants

namespace Maxwell.Certificate.FFTWitness
open Maxwell.Certificate FourierBinding

'''
    tables += f'def roots : Fin 20 → DyadicRectangle := {vector(roots)}\n\n'
    for n in (10, 20):
        tables += f'def norm{n} : DyadicRectangle := {literal(norms[n])}\n\n'
        tables += f'def coefficients{n} : Fin 20 → DyadicRectangle := {vector(kernels[n])}\n\n'
    tables += '''def root (m : ℤ) : DyadicRectangle := roots ⟨(m % 20).toNat, by omega⟩
def kernel20 : DyadicFFT.Kernel 20 := fun a b =>
  coefficients20 ⟨(a.val*b.val)%20, Nat.mod_lt _ (by decide)⟩
def kernel10 : DyadicFFT.Kernel 10 := fun a b =>
  coefficients10 ⟨(2*a.val*b.val)%20, Nat.mod_lt _ (by decide)⟩
def twiddle : DyadicFFT.Field := fun p => root ((p.1.val : ℤ)*(p.2.1.val+p.2.2.val))

end Maxwell.Certificate.FFTWitness
'''
    (OUT / 'ConstantsData.lean').write_text(tables)
    for i in range(20):
        (OUT / f'Root{i:02}.lean').write_text(f'''import Maxwell.Certificate.FFTWitness.ConstantsData

namespace Maxwell.Certificate.FFTWitness
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem root{i:02}_checked : Trigonometric.cisCheck ({i}/20)
    ((roots {i}).toRectangle 52) = true := by decide +kernel
end Maxwell.Certificate.FFTWitness
''')
    complete = 'import Maxwell.Certificate.FFTWitness.ConstantsSound\n'
    complete += ''.join(f'import Maxwell.Certificate.FFTWitness.Root{i:02}\n' for i in range(20))
    complete += '''
namespace Maxwell.Certificate.FFTWitness
open Matrix FourierBinding Maxwell.Spectral.PrimitiveYee

theorem roots_checked (i : Fin 20) : Trigonometric.cisCheck ((i.val : ℚ)/20)
    ((roots i).toRectangle 52) = true := by
  fin_cases i
'''
    complete += ''.join(f'  · exact root{i:02}_checked\n' for i in range(20))
    complete += '''
theorem root_contains (m : ℤ) : (root m).Contains 52 (root20 m) :=
  root_contains_of_checked roots_checked m

theorem kernel20_contains : DyadicFFT.KernelContains 52 kernel20 (cyclicFourier 20) :=
  kernel20_contains_of_roots root_contains

theorem kernel10_contains : DyadicFFT.KernelContains 52 kernel10 (cyclicFourier 10) :=
  kernel10_contains_of_roots root_contains

theorem twiddle_contains : DyadicFFT.Contains 52 twiddle fccTwiddle :=
  twiddle_contains_of_roots root_contains

theorem checked_inverse (input : DyadicFFT.Field) (w : DyadicFFT.Proposal)
    (v : Cell → ℂ) (hv : DyadicFFT.Contains 52 input v)
    (h : DyadicFFT.inverseCheck 52 52 kernel20 kernel10 twiddle input w = true) :
    DyadicFFT.Contains 52 w.result (transform 0 *ᵥ v) :=
  DyadicFFT.inverseCheck_sound _ _ _ _ _ kernel20_contains kernel10_contains
    twiddle_contains _ hv h

theorem checked_forward (input : DyadicFFT.Field) (w : DyadicFFT.Proposal)
    (v : Cell → ℂ) (hv : DyadicFFT.Contains 52 input v)
    (h : DyadicFFT.forwardCheck 52 52 kernel20 kernel10 twiddle input w = true) :
    DyadicFFT.Contains 52 w.result ((transform 0).conjTranspose *ᵥ v) :=
  DyadicFFT.forwardCheck_sound _ _ _ _ _ kernel20_contains kernel10_contains
    twiddle_contains _ hv h

end Maxwell.Certificate.FFTWitness
'''
    (OUT / 'Constants.lean').write_text(complete)
    (EVIDENCE / 'coefficients.json').write_text(json.dumps({'precision': 52, 'roots': roots,
        'normalizations': norms, 'normalized_root_tables': kernels}, indent=2)+'\n')
    return roots, kernels


def axis_stage(a, axis, coeff):
    output = np.empty_like(a)
    for x in range(20):
        for y in range(10):
            for z in range(10):
                row = (x,y,z)
                index = row[axis]
                terms = []
                for j in range(a.shape[axis]):
                    source = list(row)
                    source[axis] = j
                    terms.append((a[tuple(source)], coeff[index][j]))
                output[row] = round_dot(terms)
    return output


def inverse_stages(a, roots, kernels):
    k10 = [[conjugate(kernels[10][(2*i*j)%20]) for j in range(10)] for i in range(10)]
    k20 = [[conjugate(kernels[20][(i*j)%20]) for j in range(20)] for i in range(20)]
    first = axis_stage(a, 2, k10)
    second = axis_stage(first, 1, k10)
    third = np.empty_like(a)
    for x in range(20):
        for y in range(10):
            for z in range(10):
                third[x,y,z] = round_dot([(second[x,y,z], conjugate(roots[x*(y+z)%20]))])
    result = axis_stage(third, 0, k20)
    return first, second, third, result


def field_literal(a):
    return '![' + ',\n'.join('![' + ',\n'.join(vector(a[x,y]) for y in range(10)) + ']'
                            for x in range(20)) + ']'


def emit_field(prefix, stage, a):
    name = f'{prefix}{stage}'
    source = f'''import Maxwell.Certificate.FFTWitness.ConstantsData

namespace Maxwell.Certificate.FFTWitness
set_option maxRecDepth 100000

noncomputable def {name}Data : Fin 20 → Fin 10 → Fin 10 → DyadicRectangle :=
  {field_literal(a)}

noncomputable def {name} : DyadicFFT.Field := fun p => {name}Data p.1 p.2.1 p.2.2
end Maxwell.Certificate.FFTWitness
'''
    (OUT / f'{name}.lean').write_text(source)
    return name


def emit_checks(prefix, names, x_chunks, grouped=True):
    checks = [('Z', 'Input', 'First', 10), ('Y', 'First', 'Second', 10),
              ('T', 'Second', 'Third', 1), ('X', 'Third', 'Result', 20)]
    modules = []
    for axis, before, after, size in checks:
        bn, an = names[before], names[after]
        header = f'''import Maxwell.Certificate.FFTWitness.{bn}
import Maxwell.Certificate.FFTWitness.{an}

namespace Maxwell.Certificate.FFTWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0

'''
        blocks = []
        for x in range(20) if x_chunks else [None]:
            suffix = f'X{x:02}' if x is not None else 'All'
            name = f'{prefix}Check{axis}{suffix}'
            point = f'({x}, y, z)' if x is not None else '(x, y, z)'
            if axis == 'T':
                expression = f'DyadicRectangle.rescaleCheck 52 52 (DyadicRectangle.mulExact ({bn} {point}) ((twiddle {point}).conjugate)) ({an} {point})'
            else:
                row = {'X': (str(x) if x is not None else 'x'), 'Y': 'y', 'Z': 'z'}[axis]
                sourcepoint = {'X': '(j, y, z)', 'Y': f'({x if x is not None else "x"}, j, z)',
                               'Z': f'({x if x is not None else "x"}, y, j)'}[axis]
                expression = f'DyadicRectangle.dotCheck 52 52 (fun j : Fin {size} => {bn} {sourcepoint}) (fun j => (kernel{size} j {row}).conjugate) ({an} {point})'
            quantifiers = '(y z : Fin 10)' if x is not None else '(x : Fin 20) (y z : Fin 10)'
            proof = 'revert y z\n  decide +kernel' if x is not None else 'fin_cases x <;> revert y z <;> decide +kernel'
            declaration = f'''theorem {name}_accepted {quantifiers} :
    {expression} = true := by
  {proof}

'''
            if grouped and x_chunks:
                blocks.append(declaration)
            else:
                (OUT / f'{name}.lean').write_text(header + declaration + 'end Maxwell.Certificate.FFTWitness\n')
                modules.append(name)
        if blocks:
            name = f'{prefix}Check{axis}Blocks'
            (OUT / f'{name}.lean').write_text(header + ''.join(blocks) + 'end Maxwell.Certificate.FFTWitness\n')
            modules.append(name)
    return modules


def emit_complete(prefix, modules, x_chunks, native_bridge=False):
    name = f'{prefix}Complete'
    source = 'import Maxwell.Certificate.FFTWitness.Constants\nimport Maxwell.Certificate.DyadicFFTRows\n'
    source += ''.join(f'import Maxwell.Certificate.FFTWitness.{m}\n' for m in modules if 'Check' in m)
    if native_bridge:
        source += f'import Maxwell.Certificate.FFTWitness.{prefix}NativeCheck\n'
    source += f'''
namespace Maxwell.Certificate.FFTWitness
open Matrix FourierBinding Maxwell.Spectral.PrimitiveYee

noncomputable def {prefix}Proposal : DyadicFFT.Proposal :=
  ⟨{prefix}First, {prefix}Second, {prefix}Third, {prefix}Result⟩

theorem {prefix}_accepted : DyadicFFT.inverseCheck 52 52 kernel20 kernel10 twiddle
    {prefix}Input {prefix}Proposal = true := by
  apply DyadicFFT.inverseCheck_of_stages
'''
    for axis in ['Z', 'Y', 'T', 'X']:
        lemma = 'diagonalCheck_of_rows' if axis == 'T' else f'axis{axis}Check_of_rows'
        source += f'  · apply DyadicFFT.{lemma}\n    rintro ⟨x, y, z⟩\n'
        if x_chunks:
            source += '    fin_cases x\n'
            source += ''.join(f'    · exact {prefix}Check{axis}X{x:02}_accepted y z\n' for x in range(20))
        else:
            source += f'    exact {prefix}Check{axis}All_accepted x y z\n'
    source += f'''
/-- Every field enclosed by the frozen curl input has its actual inverse FCC
Fourier transform in the final proposed rectangles. -/
theorem {prefix}_inverse_contains (v : Cell → ℂ)
    (hv : DyadicFFT.Contains 52 {prefix}Input v) :
    DyadicFFT.Contains 52 {prefix}Result (transform 0 *ᵥ v) :=
  checked_inverse _ _ _ hv {prefix}_accepted

'''
    if native_bridge:
        source += f'''
/-- The existing native intermediate is accepted only through the checked
stage chain and this final integer rectangle-inclusion check. -/
theorem {prefix}_native_inverse_contains (v : Cell → ℂ)
    (hv : DyadicFFT.Contains 52 {prefix}Input v) :
    DyadicFFT.Contains 52 {prefix}Native (transform 0 *ᵥ v) := by
  intro r
  exact DyadicRectangle.subsetCheck_sound
    ({prefix}NativeCheck_accepted r.1 r.2.1 r.2.2)
    ({prefix}_inverse_contains v hv r)

'''
    source += 'end Maxwell.Certificate.FFTWitness\n'
    (OUT / f'{name}.lean').write_text(source)
    return name


def emit_native_check(prefix):
    name = f'{prefix}NativeCheck'
    (OUT/f'{name}.lean').write_text(f'''import Maxwell.Certificate.FFTWitness.{prefix}Result
import Maxwell.Certificate.FFTWitness.{prefix}Native

namespace Maxwell.Certificate.FFTWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem {name}_accepted (x : Fin 20) (y z : Fin 10) :
    DyadicRectangle.subsetCheck ({prefix}Result (x,y,z))
      ({prefix}Native (x,y,z)) = true := by
  fin_cases x <;> revert y z <;> decide +kernel

end Maxwell.Certificate.FFTWitness
''')
    return name


def emit_batch_complete(native_bridge):
    labels = ['Lower', 'Upper']
    prefixes = [f'{label}D{d}C{c:02}' for label in labels for d in range(3) for c in range(28)]
    source = ''.join(f'import Maxwell.Certificate.FFTWitness.{prefix}Complete\n' for prefix in prefixes)
    source += '''
namespace Maxwell.Certificate.FFTWitness
open Matrix FourierBinding Maxwell.Spectral.PrimitiveYee

/-- Label 0 is the lower material shift, label 1 the upper material shift. -/
abbrev PointLabel := Fin 2

'''
    for name, suffix in [('curlInput', 'Input'), ('inverseCurl', 'Native' if native_bridge else 'Result')]:
        values = '![' + ',\n'.join('![' + ',\n'.join('![' + ', '.join(
            f'{label}D{d}C{c:02}{suffix}' for c in range(28)) + ']'
            for d in range(3)) + ']' for label in labels) + ']'
        source += f'noncomputable def {name} : PointLabel → Fin 3 → Fin 28 → DyadicFFT.Field :=\n  {values}\n\n'
    source += '''/-- All 168 frozen scalar curl columns have a checked inverse transform.
Only containment of the input field remains for the preceding curl stage. -/
theorem inverseCurl_contains (label : PointLabel) (d : Fin 3) (c : Fin 28)
    (v : Cell → ℂ) (hv : DyadicFFT.Contains 52 (curlInput label d c) v) :
    DyadicFFT.Contains 52 (inverseCurl label d c) (transform 0 *ᵥ v) := by
  fin_cases label <;> fin_cases d <;> fin_cases c
'''
    for prefix in prefixes:
        suffix = '_native_inverse_contains' if native_bridge else '_inverse_contains'
        source += f'  · exact {prefix}{suffix} v hv\n'
    source += '\nend Maxwell.Certificate.FFTWitness\n'
    (OUT/'InverseComplete.lean').write_text(source)
    return 'InverseComplete'


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--constants-only', action='store_true')
    p.add_argument('--label', choices=['lower', 'upper', 'both'], default='both')
    p.add_argument('--columns', type=int, default=28)
    p.add_argument('--directions', type=int, default=3)
    p.add_argument('--whole-column-checks', action='store_true')
    p.add_argument('--split-x-modules', action='store_true')
    p.add_argument('--native-bridge', action='store_true',
                   help='Also propose/check inclusion in the original native inverse FFT output')
    args = p.parse_args()
    roots, kernels = coefficients()
    if args.constants_only:
        return
    modules = []
    records = []
    native = None
    native_inputs = {}
    if args.native_bridge:
        path = ROOT.parent/'certificates/yee/work/bulk/edge_isolation/interval_tools.py'
        spec = importlib.util.spec_from_file_location('interval_tools', path)
        native = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(native)
        library = path.with_name('interval_kernel.so')
        native_inputs = {str(path): sha256(path.read_bytes()).hexdigest(),
                         str(library): sha256(library.read_bytes()).hexdigest()}
    for label in ['lower', 'upper'] if args.label == 'both' else [args.label]:
        path = ROOT / f'evidence/point_inertia_proposals/{label}.npz'
        data = np.load(path)
        source = data['curl']
        assert source.shape == (2000, 3, 28, 3), source.shape
        saved = {name: np.zeros_like(source) for name in ['input', 'first', 'second', 'third', 'result']}
        native_result = native.fft(source, True) if native is not None else None
        for d in range(args.directions):
            for col in range(args.columns):
                a = source[:, d, col, :].reshape(20,10,10,3)
                stages = (a, *inverse_stages(a, roots, kernels))
                prefix = f'{label.title()}D{d}C{col:02}'
                names = {}
                for name, values in zip(saved, stages, strict=True):
                    saved[name][:, d, col, :] = values.reshape(2000,3)
                    names[name.title()] = emit_field(prefix, name.title(), values)
                    modules.append(names[name.title()])
                check_modules = emit_checks(prefix, names, not args.whole_column_checks,
                                            not args.split_x_modules)
                if native_result is not None:
                    modules.append(emit_field(prefix, 'Native', native_result[:,d,col,:].reshape(20,10,10,3)))
                    modules.append(emit_native_check(prefix))
                modules.extend(check_modules)
                modules.append(emit_complete(prefix, check_modules, not args.whole_column_checks,
                                             native_result is not None))
                print(f'Proposed {prefix}: radius {int(stages[-1][...,2].max())}', flush=True)
        target = EVIDENCE / f'{label}.npz'
        if native_result is not None:
            saved['native'] = native_result
        np.savez_compressed(target, **saved)
        records.append({'label': label, 'input_sha256': sha256(path.read_bytes()).hexdigest(),
                        'output_sha256': sha256(target.read_bytes()).hexdigest(),
                        'directions': args.directions, 'columns': args.columns})
    if args.label == 'both' and args.columns == 28 and args.directions == 3:
        modules.append(emit_batch_complete(args.native_bridge))
    manifest = {'precision':52, 'operation':'inverse FCC Fourier transform of frozen curl columns',
                'proof_status':'Proposed only; acceptance requires each generated Lean kernel check',
                'records':records, 'modules': modules, 'native_proposal_source': native_inputs}
    (EVIDENCE/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')


if __name__ == '__main__':
    main()
