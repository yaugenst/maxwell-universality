# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Propose exact first-derivative actions on the two actual point vectors."""
import importlib.util
import json
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/'certificates/yee/results/defects'
OUT=ROOT/'Maxwell/Certificate/BPointWitness';OUT.mkdir(exist_ok=True)


def load_witnesses():
    spec=importlib.util.spec_from_file_location('bpoint_arithmetic',SOURCE/'exact_edge_arithmetic.py')
    ar=importlib.util.module_from_spec(spec);spec.loader.exec_module(ar)
    material=json.loads((SOURCE/'inversion_edge_material.json').read_text())
    model=ar.ExactFiber((1,1,0),material['full_conventional_perturbation_numerators'])
    with np.load(SOURCE/'explore_inversion_edge_feshbach.npz',allow_pickle=False) as data:
        u=[model.project(ar.quantize(data['inversion_perturbed_eigenvectors'][:,a]),1) for a in range(2)]
    bu=[ar.apply_rows(model.B[i],u[a]) for i in range(3) for a in range(2)]
    return model,u,bu


def vec(v):return '!['+', '.join(v)+']'


def main():
    _,_,bu=load_witnesses()
    for j,values in enumerate(bu):
        body=['import Maxwell.Certificate.DerivativeInteger\n',
              'namespace Maxwell.Certificate.BPointWitness\nopen Maxwell.Spectral.PrimitiveYee\n',
              'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n']
        for d in range(3):
            for x in range(20):
                rows=[vec([str(int(values[d*2000+x*100+y*10+z])) for z in range(10)]) for y in range(10)]
                body.append(f'def rhs{j}_{d}_{x} : Fin 10 → Fin 10 → ℤ := {vec(rows)}\n')
        rows=[vec([f'rhs{j}_{d}_{x}' for x in range(20)]) for d in range(3)]
        body.append(f'def rhs{j} (e : Electric) : ℤ := ({vec(rows)}) e.1 e.2.1 e.2.2.1 e.2.2.2\n')
        body.append('end Maxwell.Certificate.BPointWitness\n')
        (OUT/f'Rhs{j}.lean').write_text('\n'.join(body))
        headers=[f'import Maxwell.Certificate.BPointWitness.Rhs{j}\n',
              f'import Maxwell.Certificate.PointWitness.Numerator{j%2}\n',
              'namespace Maxwell.Certificate.BPointWitness\nopen Maxwell.Spectral.PrimitiveYee\n',
              'open Maxwell.Certificate.DerivativeBinding\n',
              'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n']
        imports=[]
        for d in range(3):
            for x in range(20):
                mod=f'Action{j}D{d}X{x:02d}'
                imports.append(f'import Maxwell.Certificate.BPointWitness.{mod}\n')
                body=headers+[f'''theorem rhs{j}_action_{d}_{x} : ∀ (y z : Fin 10),
    BActionI ![1,1,0] {j//2} PointWitness.numerator{j%2} ({d},({x},y,z)) = rhs{j} ({d},({x},y,z)) := by
  decide +kernel
''','end Maxwell.Certificate.BPointWitness\n']
                (OUT/f'{mod}.lean').write_text('\n'.join(body))
        body=imports+['namespace Maxwell.Certificate.BPointWitness\nopen Maxwell.Spectral.PrimitiveYee\n',
                     'open Maxwell.Certificate.DerivativeBinding\n',f'''theorem rhs{j}_action (e : Electric) :
    BActionI ![1,1,0] {j//2} PointWitness.numerator{j%2} e = rhs{j} e := by
  rcases e with ⟨d,x,y,z⟩
  fin_cases d <;> fin_cases x
''']
        body.extend(f'  · exact rhs{j}_action_{d}_{x} y z\n' for d in range(3) for x in range(20))
        body.append('end Maxwell.Certificate.BPointWitness\n')
        (OUT/f'Action{j}.lean').write_text('\n'.join(body))
    print('Generated6 exact B_i U_a derivative RHS tables and kernel action proofs.')


if __name__=='__main__':main()
