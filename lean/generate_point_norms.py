# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Emit exact squared norm proposals for the actual dyadic point witnesses."""
import runpy
from pathlib import Path
s = runpy.run_path(str(Path(__file__).with_name('generate_point_witness.py')))
OUT=s['OUT']; vec=s['vector'];model=s['model']; proposals=s['proposals'];images=s['images']
(OUT/'NormDefs.lean').write_text('''import Maxwell.Certificate.IntegerAction
namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral.PrimitiveYee

def blockNormI (v : Electric → ℤ) (j : Fin 3) (x : Fin 20) : ℤ :=
  ∑ y : Fin 10, ∑ z : Fin 10, v (j,(x,y,z)) * v (j,(x,y,z))
def squareNormI (v : Electric → ℤ) : ℤ := ∑ j, ∑ x, blockNormI v j x

theorem squareNormI_eq_sum (v : Electric → ℤ) : squareNormI v = ∑ e, v e * v e := by
  simp only [squareNormI, blockNormI, Fintype.sum_prod_type]
end Maxwell.Certificate.PointWitness
''')
for a in range(2):
    stats=model.eigen_residual(proposals[a]); lam=stats['lambda_numerator']
    rs=[image*(2**51)-lam*v for image,v in zip(images[a],proposals[a])]
    for kind,values in [('Norm',proposals[a]),('Residual',rs)]:
        block=[[sum(int(v)**2 for v in values[j*2000+x*100:j*2000+x*100+100]) for x in range(20)] for j in range(3)]
        name=f'{kind.lower()}{a}'; fun=f'numerator{a}' if kind=='Norm' else f'residual{a}'
        total=sum(sum(row) for row in block)
        body=[f'import Maxwell.Certificate.PointWitness.Numerator{a}\n',
              'import Maxwell.Certificate.PointWitness.NormDefs\n']
        if kind=='Residual': body.append(f'import Maxwell.Certificate.PointWitness.Imagenumerator{a}\n')
        body.extend(['namespace Maxwell.Certificate.PointWitness\n','open Maxwell.Spectral.PrimitiveYee\n',
                     'set_option maxRecDepth 100000\n','set_option maxHeartbeats 0\n'])
        if kind=='Residual':
            body.append(f'def lambdaNumerator{a} : ℤ := {lam}\n')
            body.append(f'def residual{a} (e : Electric) : ℤ := imageNumerator{a} e * 2^51 - lambdaNumerator{a} * numerator{a} e\n')
        body.append(f'def {name}Blocks : Fin 3 → Fin 20 → ℤ := {vec([vec([str(v) for v in row]) for row in block])}\n')
        body.append(f'theorem {name}Blocks_checked (j : Fin 3) (x : Fin 20) : blockNormI {fun} j x = {name}Blocks j x := by\n  fin_cases j <;> fin_cases x <;> decide +kernel\n')
        body.append(f'theorem {name}_checked : squareNormI {fun} = {total} := by\n  unfold squareNormI\n  simp_rw [{name}Blocks_checked]\n  decide +kernel\n')
        body.append('end Maxwell.Certificate.PointWitness\n')
        (OUT/f'{kind}{a}.lean').write_text('\n'.join(body))
