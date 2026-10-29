import Maxwell.Certificate.InversionInteger
import Maxwell.Certificate.PointWitness.Vector
import Maxwell.Spectral.YeeInversion

namespace Maxwell.Certificate.PrimitiveBinding
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee Maxwell.Spectral.YeeInversion
open Maxwell.Certificate.PointWitness
open Maxwell.Spectral.PeriodicYee (Direction)
open Matrix
noncomputable section

theorem componentBlock_mulVec (D : Direction → Matrix Cell Cell ℂ)
    (v : Electric → ℂ) (e : Electric) :
    (componentBlock D *ᵥ v) e = (D e.1 *ᵥ (fun p => v (e.1,p))) e.2 := by
  rcases e with ⟨a,p⟩
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  fin_cases a <;> simp [componentBlock]

/-- Literal integer parity checks refer to the actual unitary electric inversion. -/
theorem integerVector_inversion (k : Translation) (v : Electric → ℤ) (d : ℝ) :
    electricIsometry k (integerVector v d) = integerVector (electricInversionActionI k v) d := by
  ext e
  change (electricInversion k *ᵥ (fun e => (v e : ℂ) / (d : ℂ))) e = _
  rw [electricInversion, componentBlock_mulVec, Matrix.neg_mulVec]
  simp only [Pi.neg_apply, reflection_mulVec, extend, reflectRaw, character_timeReversal,
    integerVector_apply, electricInversionActionI]
  rw [neg_one_zpow_eq_ite]
  split_ifs <;> norm_num [neg_div]

theorem integerVector_parity (k : Translation) (v : Electric → ℤ) (d : ℝ) (s : ℤ)
    (h : ∀ e, electricInversionActionI k v e = s * v e) :
    electricIsometry k (integerVector v d) = (s : ℂ) • integerVector v d := by
  rw [integerVector_inversion]
  ext e
  simp only [integerVector_apply, PiLp.smul_apply, smul_eq_mul, h, Int.cast_mul]
  ring

end
end Maxwell.Certificate.PrimitiveBinding
