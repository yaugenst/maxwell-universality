import Maxwell.Continuum.CalibrationCouplingInterval
import Maxwell.Continuum.CalibrationSandwichPrecision

/-! A finite rational quadratic value yields an interval for the
literal continuum auxiliary eigenvalue. Its error is paid for by the
proved mode and operator accuracies, without spectral evaluation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open EffectiveMass MasterConstants

attribute [local irreducible] Sh muH realMode Auxiliary.resolvent Bloch.unitary

theorem eigenvalue_approximation {L : ℝ} {z : ℝ} (hL : Ls ≤ L)
    (D : Auxiliary.Calibration L⁻¹ z) (B : FieldL2 →L[ℂ] FieldL2) (v : FieldL2)
    {ε δ : ℝ} (hv : ‖v-realMode D (inverse_length_le_1024 hL)‖ ≤ ε) (hε : ε ≤ 1)
    (hB : ‖B-Sh D‖ ≤ δ) :
    |(inner ℂ v (B v)).re-muH D (inverse_length_le_1024 hL)| ≤ 12*L^2*ε+4*δ := by
  have hS : ‖Sh D‖ ≤ 4*L^2 := by simpa only [inv_pow,inv_inv] using Sh_norm_le D
  have h := quadratic_approximation (Sh D) B (realMode D (inverse_length_le_1024 hL)) v
    hS (realMode_norm D (inverse_length_le_1024 hL)) hv hε hB
  have hi : inner ℂ (realMode D (inverse_length_le_1024 hL))
      (Sh D (realMode D (inverse_length_le_1024 hL))) =
      (muH D (inverse_length_le_1024 hL) : ℂ) := by
    rw [realMode_eigen,inner_smul_right,inner_self_eq_norm_sq_to_K,realMode_norm]
    simp
  rw [hi] at h
  apply (Complex.abs_re_le_norm (inner ℂ v (B v)-(muH D (inverse_length_le_1024 hL) : ℂ))).trans
  convert! h using 1
  ring

theorem eigenvalue_interval {L : ℝ} {z : ℝ} (hL : Ls ≤ L)
    (D : Auxiliary.Calibration L⁻¹ z) (N ell P : ℕ) (hlog : L ≤ (2 : ℝ)^ell)
    (hP : cutoffWorkBits (N+1) ell ≤ P)
    (B : FieldL2 →L[ℂ] FieldL2) (v : FieldL2) (c : ℚ)
    (hv : ‖v-realMode D (inverse_length_le_1024 hL)‖ ≤ (1/2 : ℝ)^P)
    (hB : ‖B-Sh D‖ ≤ (1/2 : ℝ)^P)
    (hc : (c : ℝ)=(inner ℂ v (B v)).re) :
    (couplingInterval c N).Contains (muH D (inverse_length_le_1024 hL)) := by
  apply couplingInterval_contains
  rw [hc]
  apply (eigenvalue_approximation hL D B v hv
    (pow_le_one₀ (by norm_num) (by norm_num)) hB).trans
  apply le_trans _ (sandwich_precision_error (length_ge_one hL) (N+1) ell P hlog hP)
  have hL1 := length_ge_one hL
  have hsq : 1 ≤ L^2 := by nlinarith
  have hp : (0 : ℝ) ≤ (1/2 : ℝ)^P := by positivity
  nlinarith

#print axioms eigenvalue_interval

end Maxwell.Continuum.Calibration
