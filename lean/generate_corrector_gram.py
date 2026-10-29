# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Propose exact corrector Gram data and its LDL norm certificate."""
import runpy
from pathlib import Path
ROOT=Path(__file__).resolve().parent
s=runpy.run_path(str(ROOT/'generate_corrector_witness.py'))
model,y,images=s['load_witnesses']();OUT=s['OUT'];vec=s['vector']
h=runpy.run_path(str(ROOT/'generate_finite_witnesses.py'));Q=h['Q'];mat=h['mat'];ldl=h['ldl'];rational=h['rational']
gram=[[sum(int(a)*int(b) for a,b in zip(v,w)) for w in y] for v in y]
for i in range(6):
 for j in range(i,6):
    blocks=[[sum(int(y[i][k])*int(y[j][k]) for k in range(d*2000+x*100,d*2000+x*100+100)) for x in range(20)] for d in range(3)]
    name=f'dot{i}{j}'
    body=f'''import Maxwell.Certificate.CorrectorWitness.Numerator{i}
import Maxwell.Certificate.CorrectorWitness.Numerator{j}
import Maxwell.Certificate.PointWitness.DotDefs
namespace Maxwell.Certificate.CorrectorWitness
open Maxwell.Certificate.PointWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def {name}Blocks : Fin 3 → Fin 20 → ℤ := {vec([vec([str(v) for v in row]) for row in blocks])}
theorem {name}Blocks_checked (d : Fin 3) (x : Fin 20) :
    blockDotI numerator{i} numerator{j} d x = {name}Blocks d x := by
  fin_cases d <;> fin_cases x <;> decide +kernel

theorem {name}_checked : dotI numerator{i} numerator{j} = {gram[i][j]} := by
  unfold dotI
  simp_rw [{name}Blocks_checked]
  decide +kernel
'''
    if i!=j:
        body+=f'''\ntheorem dot{j}{i}_checked : dotI numerator{j} numerator{i} = {gram[i][j]} := by
  have h : dotI numerator{j} numerator{i} = dotI numerator{i} numerator{j} := by
    simp only [dotI_eq_sum, mul_comm]
  rw [h, {name}_checked]
'''
    body+='\nend Maxwell.Certificate.CorrectorWitness\n'
    (OUT/f'Dot{i}{j}.lean').write_text(body)
imports='\n'.join(f'import Maxwell.Certificate.CorrectorWitness.Dot{i}{j}' for i in range(6) for j in range(i,6))
qgram=[[Q(v,2**202) for v in row] for row in gram]
lemmas=', '.join(f'dot{i}{j}_checked' for i in range(6) for j in range(6))
body=imports+f'''
import Maxwell.Certificate.PointWitness.Inner
import Maxwell.Certificate.Matrix
namespace Maxwell.Certificate.CorrectorWitness
open Maxwell.Spectral.PrimitiveYee
open Maxwell.Certificate.PointWitness
noncomputable section

def numerators : Fin 6 → Electric → ℤ := {vec([f'numerator{i}' for i in range(6)])}
def gram : Matrix (Fin 6) (Fin 6) ℝ := {mat(qgram)}

theorem gram_binding (i j : Fin 6) :
    inner ℂ (integerVector (numerators i) (2^101))
      (integerVector (numerators j) (2^101)) = (gram i j : ℂ) := by
  rw [integerVector_inner]
  fin_cases i <;> fin_cases j <;>
    norm_num [numerators, gram, {lemmas}]

end
end Maxwell.Certificate.CorrectorWitness
'''
(OUT/'Gram.lean').write_text(body)
for bound, filename, declaration in [(Q(361), "GramBound", "gram_bound_psd"), (Q(1369,4), "GramSharpBound", "gram_sharp_bound_psd")]:
    a=[[bound*Q(i==j)-qgram[i][j] for j in range(6)] for i in range(6)]
    ll,dd=ldl(a)
    body=f'''import Maxwell.Certificate.CorrectorWitness.Gram
    namespace Maxwell.Certificate.CorrectorWitness
    noncomputable section
    open Matrix
    set_option maxRecDepth 100000
    set_option maxHeartbeats 0
    private def gramBoundL : Matrix (Fin 6) (Fin 6) ℝ := {mat(ll)}
    private def gramBoundD : Fin 6 → ℝ := {vec([rational(x) for x in dd])}
    theorem {declaration} : (({rational(bound)} : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - gram).PosSemidef := by
      apply real_ldl_sound _ gramBoundL gramBoundD
      · ext i j
        simp only [ldl_apply]
        fin_cases i <;> fin_cases j <;> norm_num [gram, gramBoundL, gramBoundD,
          Fin.sum_univ_succ, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply,
          Matrix.one_apply, Matrix.vecHead, Matrix.vecTail]
      · intro i
        fin_cases i <;> norm_num [gramBoundD]
    end
    end Maxwell.Certificate.CorrectorWitness
    '''
    (OUT/f'{filename}.lean').write_text(body.replace('\n    ', '\n'))
print('Generated21 exact6000-term Gram dot products and the6x6 LDL norm bound.')
