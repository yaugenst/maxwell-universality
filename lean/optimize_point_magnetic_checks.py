# /// script
# requires-python = ">=3.11"
# ///
"""Replace uncompiled magnetic arithmetic by its proved force-once checker.

Public propositions and existing literal tables remain unchanged. Refuse to
rewrite any compiled action source; accepted earlier columns are retained.
"""
from pathlib import Path
import argparse
import re

ROOT = Path(__file__).resolve().parent

def main():
    p = argparse.ArgumentParser()
    p.add_argument('label', choices=['Lower','Upper'])
    p.add_argument('first', type=int)
    args = p.parse_args()
    for col in range(args.first,28):
        prefix = f'{args.label}C{col:02d}'
        relative = f'Maxwell/Certificate/PointActionWitness/{prefix}'
        if (ROOT/f'.lake/build/lib/lean/{relative}.olean').exists():
            continue
        path = ROOT/f'{relative}.lean'
        text = path.read_text()
        if 'DyadicKernelMagneticSound' in text:
            continue
        text = 'import Maxwell.Certificate.DyadicKernelMagneticSound\n' + text
        for x in range(20):
            old = (f'theorem {prefix}CheckX{x} : ∀ y z : Fin 10, '
                   f'{prefix}Check ({x},y,z) = true := by decide +kernel')
            new = (f'theorem {prefix}CheckX{x} : ∀ y z : Fin 10, '
                   f'{prefix}Check ({x},y,z) = true := by\n'
                   f'  have h : ∀ y z : Fin 10, DyadicKernel.magneticCheck\n'
                   f'      ⟨DyadicKernel.Triple.ofVector (symbolEnclosure ({x},y,z)),\n'
                   f'       DyadicKernel.Triple.ofVector ({prefix}Weighted ({x},y,z)),\n'
                   f'       DyadicKernel.Triple.ofVector ({args.label}Result{col} ({x},y,z)),\n'
                   f'       DyadicKernel.Triple.ofVector ({args.label}Applied{col} ({x},y,z))⟩ = true := by\n'
                   f'    decide +kernel\n'
                   f'  intro y z\n'
                   f'  exact DyadicKernel.magneticCheck_of_vector _ _ _ _ (h y z)')
            assert text.count(old) == 1, (path,x)
            text = text.replace(old,new)
        path.write_text(text)
        print(prefix,flush=True)

if __name__ == '__main__':
    main()
