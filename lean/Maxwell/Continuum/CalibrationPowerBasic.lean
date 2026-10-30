import Maxwell.Continuum.TopEigenDataTransport
import Maxwell.Continuum.TopEigenPerturbationEigen

/-! Power iteration for an actual bounded self-adjoint operator with
an isolated top eigenpair. No finite-rank or compactness premise is used. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

open TopEigenPerturbation
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {A : H →L[ℂ] H} {u : H} {mu d : ℝ} (D : Data A u mu d)

include D

theorem power_coefficient (v : H) (n : ℕ) :
    inner ℂ u ((A^n) v) = (mu : ℂ)^n*inner ℂ u v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, D.coefficient_apply, ih, pow_succ']
    ring

theorem power_eigenvector (n : ℕ) : (A^n) u = (mu : ℂ)^n • u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, D.eigenvector, smul_smul, pow_succ']
    congr 1
    ring

theorem power_complement (v : H) (hv : inner ℂ u v = 0) (n : ℕ) :
    ‖(A^n) v‖ ≤ (mu-d)^n*‖v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, pow_succ']
    have ho : inner ℂ u ((A^n) v) = 0 := by rw [power_coefficient D, hv, mul_zero]
    exact (D.complement _ ho).trans ((mul_le_mul_of_nonneg_left ih
      (sub_nonneg.mpr D.gap_le_mu)).trans_eq (mul_assoc _ _ _).symm)

theorem residual_orthogonal (v : H) : inner ℂ u (v-inner ℂ u v • u) = 0 := by
  rw [inner_sub_right, inner_smul_right, D.inner_self_one, mul_one, sub_self]

theorem residual_norm (v : H) : ‖v-inner ℂ u v • u‖ ≤ ‖v‖ := by
  have hp : ((ℂ ∙ u)ᗮ).starProjection v = v-inner ℂ u v • u := by
    rw [Submodule.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply,
      Submodule.starProjection_unit_singleton ℂ D.unit_norm]
  rw [← hp]
  exact ((ℂ ∙ u)ᗮ).norm_starProjection_apply_le v

theorem power_error (v : H) (n : ℕ) :
    ‖(A^n) v-(mu : ℂ)^n • (inner ℂ u v • u)‖ ≤ (mu-d)^n*‖v‖ := by
  have hid : (A^n) (v-inner ℂ u v • u) =
      (A^n) v-(mu : ℂ)^n • (inner ℂ u v • u) := by
    rw [map_sub, map_smul, power_eigenvector D]
    congr 1
    exact smul_comm _ _ _
  rw [← hid]
  exact (power_complement D _ (residual_orthogonal D v) n).trans
    (mul_le_mul_of_nonneg_left (residual_norm D v) (pow_nonneg (sub_nonneg.mpr D.gap_le_mu) n))

theorem power_norm_lower (v : H) (n : ℕ) :
    mu^n*‖inner ℂ u v‖ ≤ ‖(A^n) v‖ := by
  have hb := norm_inner_le_norm (𝕜 := ℂ) u ((A^n) v)
  rw [D.unit_norm, one_mul, power_coefficient D, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (lt_of_lt_of_le D.gap_pos D.gap_le_mu)] at hb
  exact hb

theorem power_ne_zero (v : H) (hv : inner ℂ u v ≠ 0) (n : ℕ) : (A^n) v ≠ 0 := by
  intro hz
  have hp : 0 < mu^n*‖inner ℂ u v‖ := mul_pos
    (pow_pos (lt_of_lt_of_le D.gap_pos D.gap_le_mu) n) (norm_pos_iff.mpr hv)
  have hb := power_norm_lower D v n
  rw [hz, norm_zero] at hb
  linarith

omit D in
/-- Every approximate application has an absolute error at most `ε`.
The statement controls the actual iterates without an exact-operation oracle. -/
theorem approximate_power_error (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (v : H) (y : ℕ → H) {ε : ℝ}
    (h0 : ‖y 0-v‖ ≤ ε) (hstep : ∀ n, ‖y (n+1)-T (y n)‖ ≤ ε) (n : ℕ) :
    ‖y n-(T^n) v‖ ≤ (n+1)*ε := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    have hn := T.le_of_opNorm_le hT (y n-(T^n) v)
    rw [map_sub, one_mul] at hn
    have ht := norm_sub_le_norm_sub_add_norm_sub (y (n+1)) (T (y n)) (T ((T^n) v))
    have hb := ht.trans (add_le_add (hstep n) (hn.trans ih))
    exact hb.trans_eq (by push_cast; ring)

#print axioms power_error
#print axioms power_norm_lower
#print axioms approximate_power_error

end Maxwell.Continuum.Calibration
