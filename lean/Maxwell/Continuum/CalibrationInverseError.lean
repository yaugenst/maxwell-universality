import Maxwell.Continuum.CalibrationNeumann
import Mathlib.Analysis.Normed.Ring.Units

/-! Quantitative inversion of an approximate finite operator. A norm
bound on the true inverse and a sufficiently small operator error
construct invertibility and certify the inverse error. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem inverse_perturbation_estimate (A B : H →L[ℂ] H) (hA : IsUnit A)
    {M ε : ℝ} (hM : ‖Ring.inverse A‖ ≤ M) (hε : ‖A-B‖ ≤ ε) (hsmall : M*ε ≤ 1/2) :
    IsUnit B ∧ ‖Ring.inverse B‖ ≤ 2*M ∧
      ‖Ring.inverse A-Ring.inverse B‖ ≤ 2*M^2*ε := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  let T := (A-B)*Ring.inverse A
  have hT : ‖T‖ ≤ 1/2 :=
    (norm_mul_le _ _).trans ((mul_le_mul hε hM (norm_nonneg _) hε0).trans
      (by nlinarith [hsmall]))
  have hT1 : ‖T‖ < 1 := hT.trans_lt (by norm_num)
  have hfactor : B = (1-T)*A := by
    dsimp [T]
    rw [sub_mul,one_mul,mul_assoc,Ring.inverse_mul_cancel _ hA,mul_one]
    abel
  have hB : IsUnit B := hfactor ▸ (isUnit_one_sub_of_norm_lt_one hT1).mul hA
  have hformula : Ring.inverse B = Ring.inverse A*FreeFiber.Neumann.series T := by
    rw [hfactor,Ring.inverse_mul (Or.inr hA)]
    congr 1
    exact (geom_series_eq_inverse T hT1).symm
  have hseries : ‖FreeFiber.Neumann.series T‖ ≤ 2 := by
    apply (FreeFiber.Neumann.series_norm_le T hT1).trans
    have hden : 0 < 1-‖T‖ := by linarith
    calc
      _ ≤ (1/2 : ℝ)⁻¹ := (inv_le_inv₀ hden (by norm_num)).mpr (by linarith)
      _ = _ := by norm_num
  have hRB : ‖Ring.inverse B‖ ≤ 2*M := by
    rw [hformula]
    exact (norm_mul_le _ _).trans ((mul_le_mul hM hseries (norm_nonneg _) hM0).trans_eq (mul_comm _ _))
  refine ⟨hB,hRB,?_⟩
  have hid : Ring.inverse A-Ring.inverse B = Ring.inverse A*(B-A)*Ring.inverse B := by
    rw [mul_sub,sub_mul,mul_assoc,Ring.mul_inverse_cancel _ hB,mul_one,
      Ring.inverse_mul_cancel _ hA,one_mul]
  rw [hid]
  have hdiff : ‖B-A‖ ≤ ε := by simpa only [norm_sub_rev] using hε
  calc
    _ ≤ (‖Ring.inverse A‖*‖B-A‖)*‖Ring.inverse B‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (M*ε)*(2*M) := mul_le_mul
      (mul_le_mul hM hdiff (norm_nonneg _) hM0) hRB (norm_nonneg _) (mul_nonneg hM0 hε0)
    _ = _ := by ring

#print axioms inverse_perturbation_estimate

end Maxwell.Continuum.Calibration
