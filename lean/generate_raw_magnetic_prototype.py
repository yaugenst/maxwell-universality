# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Freeze one actual magnetic-action column with separate arithmetic and binding."""
from pathlib import Path
import argparse
import json
import numpy as np

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'Maxwell/Certificate/RawMagneticWitness'
OUT.mkdir(exist_ok=True)

def rect(a):
    return '⟨' + ','.join(str(int(x)) for x in a) + '⟩'

def triple(a):
    return '⟨' + ','.join(rect(x) for x in a) + '⟩'

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--label', choices=['Lower','Upper'], default='Lower')
    p.add_argument('--column', type=int, default=0)
    args = p.parse_args()
    label, col = args.label, args.column
    prefix = f'{label}C{col:02d}'
    with np.load(ROOT/f'evidence/point_inertia_proposals/{label.lower()}.npz') as data:
        d = data['d']
        w = data['weighted'][:,:,col]
        u = data['field'][:,:,col]
        v = data['applied'][:,:,col]
    s = ('import Maxwell.Certificate.DyadicKernelMagnetic\n'
         'namespace Maxwell.Certificate.RawMagneticWitness\n'
         'open DyadicKernel\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n')
    for x in range(20):
        rows = ['⟨' + ','.join(triple(a[f]) for a in (d,w,u,v)) + '⟩'
                for f in range(100*x,100*(x+1))]
        s += f'noncomputable def {prefix}Rows{x} : List MagneticRow := [' + ','.join(rows) + ']\n'
        s += f'theorem {prefix}Rows{x}_checked : {prefix}Rows{x}.all magneticCheck = true := by decide +kernel\n'
    s += 'end Maxwell.Certificate.RawMagneticWitness\n'
    (OUT/f'{prefix}Raw.lean').write_text(s)
    t = (f'import Maxwell.Certificate.RawMagneticWitness.{prefix}Raw\n'
         'import Maxwell.Certificate.DyadicKernelMagneticSound\n'
         f'import Maxwell.Certificate.PointActionWitness.{prefix}\n'
         'namespace Maxwell.Certificate.RawMagneticWitness\n'
         'open DyadicKernel FourierBinding PointInertia ProjectionWitness AppliedWitness\n'
         'open PointActionWitness\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n')
    t += f'noncomputable def {prefix}Row (f : Frequency) : MagneticRow :=\n'
    t += f'  ⟨Triple.ofVector (symbolEnclosure f),Triple.ofVector ({prefix}Weighted f),\n'
    t += f'   Triple.ofVector ({label}Result{col} f),Triple.ofVector ({label}Applied{col} f)⟩\n'
    for x in range(20):
        t += f'theorem {prefix}Rows{x}_bound : {prefix}Rows{x} = (List.ofFn (fun y : Fin 10 => List.ofFn (fun z : Fin 10 => {prefix}Row ({x},y,z)))).flatten := by decide +kernel\n'
    t += f'theorem {prefix}_raw_check (f : Frequency) : DyadicRectangle.magneticCheck (symbolEnclosure f) ({prefix}Weighted f) ({label}Result{col} f) ({label}Applied{col} f) = true := by\n'
    t += '  apply magneticCheck_of_vector\n  rcases f with ⟨x,y,z⟩\n  fin_cases x\n'
    for x in range(20):
        t += f'  · exact magneticCheck_of_block (fun y z => {prefix}Row ({x},y,z)) {prefix}Rows{x} {prefix}Rows{x}_bound {prefix}Rows{x}_checked y z\n'
    t += 'end Maxwell.Certificate.RawMagneticWitness\n'
    (OUT/f'{prefix}Bound.lean').write_text(t)
    evidence = ROOT/'evidence/raw_magnetic_prototype'
    evidence.mkdir(exist_ok=True)
    (evidence/f'{prefix}_modules.json').write_text(json.dumps([
        f'Maxwell.Certificate.RawMagneticWitness.{prefix}Raw',
        f'Maxwell.Certificate.RawMagneticWitness.{prefix}Bound'],indent=2)+'\n')

if __name__ == '__main__':
    main()
