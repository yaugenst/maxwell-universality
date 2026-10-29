# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Propose exact six-column corrector residual sums from frozen integer tables."""
from pathlib import Path
from generate_bpoint_witness import load_witnesses as load_point
from generate_corrector_witness import load_witnesses as load_corrector

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'Maxwell/Certificate/CorrectorWitness'
_, _, rhs = load_point()
_, proposals, images = load_corrector()
center = 11563615502041082931861
totals = []


def vec(xs):
    return '![' + ', '.join(xs) + ']'


for j in range(6):
    residual = [int(w) * 2**51 - center * int(v) - int(b) * 2**80
                for w, v, b in zip(images[j], proposals[j], rhs[j])]
    blocks = [[sum(v*v for v in residual[d*2000+x*100:d*2000+x*100+100])
               for x in range(20)] for d in range(3)]
    total = sum(map(sum, blocks))
    totals.append(total)
    body = f'''import Maxwell.Certificate.CorrectorWitness.Numerator{j}
import Maxwell.Certificate.CorrectorWitness.Imagenumerator{j}
import Maxwell.Certificate.BPointWitness.Rhs{j}
import Maxwell.Certificate.PointWitness.NormDefs
namespace Maxwell.Certificate.CorrectorWitness
open Maxwell.Spectral.PrimitiveYee
open Maxwell.Certificate.PointWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def residual{j} (e : Electric) : ℤ :=
  imageNumerator{j} e * 2^51 - {center} * numerator{j} e - BPointWitness.rhs{j} e * 2^80

def residual{j}Blocks : Fin 3 → Fin 20 → ℤ := {vec([vec([str(v) for v in row]) for row in blocks])}

theorem residual{j}Blocks_checked (d : Fin 3) (x : Fin 20) :
    blockNormI residual{j} d x = residual{j}Blocks d x := by
  fin_cases d <;> fin_cases x <;> decide +kernel

theorem residual{j}_checked : squareNormI residual{j} = {total} := by
  unfold squareNormI
  simp_rw [residual{j}Blocks_checked]
  decide +kernel

end Maxwell.Certificate.CorrectorWitness
'''
    (OUT / f'Residual{j}.lean').write_text(body)

assert sum(totals) <= 2**292
body = ''.join(f'import Maxwell.Certificate.CorrectorWitness.Residual{j}\n' for j in range(6))
body += '''import Maxwell.Certificate.PointWitness.Vector
namespace Maxwell.Certificate.CorrectorWitness
open Maxwell.Spectral.PrimitiveYee
open Maxwell.Certificate.PointWitness
noncomputable section
def residuals : Fin 6 → Electric → ℤ := ![residual0, residual1, residual2, residual3, residual4, residual5]

theorem residual_frobenius_sq :
    ∑ j : Fin 6, ‖integerVector (residuals j) (2^181)‖^2 ≤ (1 / 2^35 : ℝ)^2 := by
  simp only [integerVector_norm_sq]
  norm_num [Fin.sum_univ_succ, residuals, '''
body += ', '.join(f'residual{j}_checked' for j in range(6))
body += ''']

end
end Maxwell.Certificate.CorrectorWitness
'''
(OUT / 'ResidualBound.lean').write_text(body)
print('Generated six actual residual norm proposals; total squared residual bound holds rationally.')

for j in range(6):
    body = f'''import Maxwell.Certificate.CorrectorWitness.Action{j}Complete
import Maxwell.Certificate.CorrectorWitness.Residual{j}
import Maxwell.Certificate.BPointWitness.Action{j}
import Maxwell.Certificate.DerivativeVector
import Maxwell.Certificate.PointWitness.Bounds0
import Maxwell.Certificate.PointWitness.Bounds1
import Maxwell.Certificate.PointWitness.Fiber

namespace Maxwell.Certificate.CorrectorWitness
open Maxwell.Spectral.PrimitiveYee
open Maxwell.Certificate.PointWitness Maxwell.Certificate.DerivativeBinding
noncomputable section

theorem residual{j}_binding :
    pointOperator (integerVector numerator{j} (2^101)) -
      (pointCenter0 : ℂ) • integerVector numerator{j} (2^101) -
      BOperator ![1,1,0] {j//2} pointVector{j%2} = integerVector residual{j} (2^181) := by
  have hc : (pointCenter0 : ℂ) = ({center} : ℂ) / 2^80 := by
    norm_num [pointCenter0, lambdaNumerator0]
  rw [hc]
  exact integerVector_corrector_residual ![1,1,0] {j//2}
    PointWitness.numerator{j%2} numerator{j} imageNumerator{j} BPointWitness.rhs{j}
    {center} (funext numerator{j}_action) (funext BPointWitness.rhs{j}_action)

end
end Maxwell.Certificate.CorrectorWitness
'''
    (OUT / f'Computed{j}.lean').write_text(body)
