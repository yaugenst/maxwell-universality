# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Generate the exact cross Gram scalar of the point witnesses."""
import runpy
from pathlib import Path
s=runpy.run_path(str(Path(__file__).with_name('generate_point_witness.py')))
vec=s['vector'];OUT=s['OUT'];u,v=s['proposals']
blocks=[[sum(int(u[i])*int(v[i]) for i in range(j*2000+x*100,j*2000+x*100+100)) for x in range(20)] for j in range(3)]
body='''import Maxwell.Certificate.PointWitness.Numerator0
import Maxwell.Certificate.PointWitness.Numerator1
import Maxwell.Certificate.PointWitness.DotDefs

namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral.PrimitiveYee
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
body+=f'\ndef crossBlocks : Fin 3 → Fin 20 → ℤ := {vec([vec([str(v) for v in row]) for row in blocks])}\n'
body+='''
theorem crossBlocks_checked (j : Fin 3) (x : Fin 20) :
    blockDotI numerator0 numerator1 j x = crossBlocks j x := by
  fin_cases j <;> fin_cases x <;> decide +kernel
'''
body+=f'\ntheorem cross_checked : dotI numerator0 numerator1 = {sum(sum(row) for row in blocks)} := by\n  unfold dotI\n  simp_rw [crossBlocks_checked]\n  decide +kernel\n'
body+='\nend Maxwell.Certificate.PointWitness\n'
(OUT/'Cross.lean').write_text(body)

helpers=runpy.run_path(str(Path(__file__).with_name('generate_finite_witnesses.py')))
Q=helpers['Q']; mat=helpers['mat']; ldl=helpers['ldl']; rational=helpers['rational']
g=[[Q(sum(int(a)*int(b) for a,b in zip(ui,uj)),2**202) for uj in (u,v)] for ui in (u,v)]
for kind,bound in [('Lower',1-Q(1,10**12)),('Upper',1+Q(1,10**12))]:
    a=[[g[i][j]-bound*(i==j) if kind=='Lower' else bound*(i==j)-g[i][j] for j in range(2)] for i in range(2)]
    ll,dd=ldl(a);name='gram'+kind
    expr=f'pointGram - ({rational(bound)} : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)' if kind=='Lower' else f'({rational(bound)} : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - pointGram'
    body=f'''import Maxwell.Certificate.PointWitness.Gram
namespace Maxwell.Certificate.PointWitness
noncomputable section
open Matrix
private def {name}L : Matrix (Fin 2) (Fin 2) ℝ := {mat(ll)}
private def {name}D : Fin 2 → ℝ := {vec([rational(x) for x in dd])}
theorem {name}_psd : ({expr}).PosSemidef := by
  apply real_ldl_sound _ {name}L {name}D
  · ext i j
    simp only [ldl_apply]
    fin_cases i <;> fin_cases j <;> norm_num [pointGram, {name}L, {name}D,
      Fin.sum_univ_succ, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.vecHead, Matrix.vecTail]
  · intro i
    fin_cases i <;> norm_num [{name}D]
end
end Maxwell.Certificate.PointWitness
'''
    (OUT/f'Gram{kind}.lean').write_text(body)
