# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Bind each saved central compression to its exact signed Schur inputs."""
from pathlib import Path
import argparse
import json
import numpy as np
from generate_raw_global_schur import matrix

ROOT=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser()
    p.add_argument('index',type=int)
    args=p.parse_args()
    prefix=f'Record{args.index:04d}'
    out=ROOT/'Maxwell/Certificate/GlobalSchurWitness'
    with np.load(ROOT/f'evidence/global_center_proposals/record{args.index:04d}.npz') as data:
        compression=np.array(data['compression'],dtype=object)*16
    n=len(compression)
    text=('import Maxwell.Certificate.DyadicKernelSigned\n'
          f'import Maxwell.Certificate.GlobalSchurWitness.{prefix}NegativeRaw\n'
          f'import Maxwell.Certificate.GlobalSchurWitness.{prefix}PositiveRaw\n'
          f'namespace Maxwell.Certificate.GlobalSchurWitness.{prefix}\n'
          'open DyadicKernel\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n')
    text+=matrix('compression',compression)
    text+=f'def negativeSelect (i : Fin 2) : Fin {n} := i.castAdd {n-2}\n'
    text+=f'def positiveSelect (i : Fin {n-2}) : Fin {n} := i.natAdd 2\n'
    for tag,count,negative in [('Negative',2,'true'),('Positive',n-2,'false')]:
        select=tag.lower()+'Select'
        text+=(f'theorem {tag.lower()}_shift_checked : ∀ i j : Fin {count}, j ≤ i →\n'
               f'    subsetCheck (signedEntry {negative} (compression ({select} i) ({select} j)) i j)\n'
               f'      ({prefix}{tag}.enclosure0 i j) = true := by decide +kernel\n')
        text+=(f'theorem {tag.lower()}_upper_conjugate : ∀ i j : Fin {count}, i < j →\n'
               f'    {prefix}{tag}.enclosure0 i j = conjugate ({prefix}{tag}.enclosure0 j i) := by decide +kernel\n')
    text+=f'end Maxwell.Certificate.GlobalSchurWitness.{prefix}\n'
    (out/f'{prefix}SignedRaw.lean').write_text(text)
    sound=(f'import Maxwell.Certificate.GlobalSchurWitness.{prefix}SignedRaw\n'
           'import Maxwell.Certificate.GlobalSigned\n'
           f'namespace Maxwell.Certificate.GlobalSchurWitness.{prefix}\n'
           'open DyadicKernel Matrix\nopen scoped ComplexOrder\n')
    for tag,negative in [('Negative','true'),('Positive','false')]:
        select=tag.lower()+'Select'
        sound+=(f'theorem {tag.lower()}_posDef {{m : ℕ}} (F A : Matrix (Fin m) (Fin {n}) ℂ)\n'
                '    (hc : ∀ i j, (compression i j).toDyadic.Contains 52\n'
                '      (HermitianCompression.matrix F A i j)) :\n'
                f'    (LowCompressionWitness.signedMatrix {negative}\n'
                f'      (HermitianCompression.matrix (F.submatrix id {select}) (A.submatrix id {select}))).PosDef :=\n'
                f'  GlobalSigned.selected_posDef F A compression {select} {negative}\n'
                f'    {prefix}{tag}.enclosure0 {prefix}{tag}.proposal0 {prefix}{tag}.accepted0\n'
                f'    hc {tag.lower()}_shift_checked {tag.lower()}_upper_conjugate\n')
    sound+=f'end Maxwell.Certificate.GlobalSchurWitness.{prefix}\n'
    (out/f'{prefix}Signed.lean').write_text(sound)
    modules=[f'Maxwell.Certificate.GlobalSchurWitness.{prefix}SignedRaw',
             f'Maxwell.Certificate.GlobalSchurWitness.{prefix}Signed']
    (ROOT/f'evidence/global_schur_proposals/{prefix}Signed_modules.json').write_text(json.dumps(modules,indent=2)+'\n')

if __name__=='__main__':
    main()
