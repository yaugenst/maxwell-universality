import Maxwell.Spectral.AnalyticEigenbranch
import Mathlib.Tactic.NoncommRing

/-! Resolvent differences on the actual complementary spectral subspace. -/

noncomputable section

namespace Maxwell.Defect

section Algebra

variable {R : Type*} [Ring R] [Algebra ℂ R]

omit [Algebra ℂ R] in
theorem commute_inverse_of_two_sided (Q A r : R)
    (hQA : Q * A = A * Q) (hAr : A * r = 1) (hrA : r * A = 1) : Q * r = r * Q := by
  calc
    Q * r = (r * A) * (Q * r) := by rw [hrA, one_mul]
    _ = r * (A * Q) * r := by simp only [mul_assoc]
    _ = r * (Q * A) * r := by rw [hQA]
    _ = r * Q := by simp only [mul_assoc, hAr, mul_one]

theorem shifted_inverse_difference (H : R) (z w : ℂ) (r s : R)
    (hr : r * (H - z • 1) = 1) (hs : (H - w • 1) * s = 1) :
    r - s = (z - w) • (r * s) := by
  have hdiff : (H - w • (1 : R)) - (H - z • 1) = (z - w) • 1 := by
    rw [sub_smul]
    abel
  calc
    r - s = r * ((H - w • 1) - (H - z • 1)) * s := by
      rw [mul_sub, sub_mul, mul_assoc r (H - w • 1) s, hs, mul_one,
        hr, one_mul]
    _ = (z - w) • (r * s) := by
      rw [hdiff, mul_smul_comm, mul_one, smul_mul_assoc]

theorem projected_inverse_difference (H Q : R) (z w : ℂ) (r s : R)
    (hQQ : Q * Q = Q) (hQH : Q * H = H * Q)
    (hr1 : (H - z • 1) * r = 1) (hr2 : r * (H - z • 1) = 1)
    (hs : (H - w • 1) * s = 1) :
    Q * r - Q * s = (z - w) • ((Q * r) * (Q * s)) := by
  have hQA : Q * (H - z • 1) = (H - z • 1) * Q := by
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hQH]
  have hQr := commute_inverse_of_two_sided Q (H - z • 1) r hQA hr1 hr2
  have hproduct : (Q * r) * (Q * s) = Q * (r * s) := by
    calc
      (Q * r) * (Q * s) = Q * (r * Q) * s := by simp only [mul_assoc]
      _ = Q * (Q * r) * s := by rw [hQr]
      _ = Q * (r * s) := by rw [← mul_assoc Q Q r, hQQ, mul_assoc]
  rw [← mul_sub, shifted_inverse_difference H z w r s hr2 hs,
    mul_smul_comm, hproduct]

omit [Algebra ℂ R] in
theorem sandwich_eq_projected_inverse (Q A r : R) (hQQ : Q * Q = Q)
    (hQA : Q * A = A * Q) (hAr : A * r = 1) (hrA : r * A = 1) :
    Q * r * Q = Q * r := by
  have hc := commute_inverse_of_two_sided Q A r hQA hAr hrA
  rw [mul_assoc, ← hc, ← mul_assoc, hQQ]

end Algebra

section Norm

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]

theorem resolvent_difference_norm_le (r s : R) (z w : ℂ) (g : ℝ) (hg : 0 < g)
    (hdifference : r - s = (z - w) • (r * s))
    (hr : ‖r‖ ≤ g⁻¹) (hs : ‖s‖ ≤ g⁻¹) :
    ‖r - s‖ ≤ ‖z - w‖ / g ^ 2 := by
  rw [hdifference, norm_smul]
  calc
    _ ≤ ‖z - w‖ * (‖r‖ * ‖s‖) := mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ‖z - w‖ * (g⁻¹ * g⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hr hs (norm_nonneg _) (inv_nonneg.mpr hg.le))
        (norm_nonneg _)
    _ = _ := by field_simp

end Norm

section ActualRegular

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

open Maxwell.Spectral.AnalyticEigenbranch

theorem regularResolvent_eq_complementary_inverse
    (T P : F →L[ℂ] F) (value z : ℂ)
    (hPP : P * P = P) (hTP : T * P = value • P) (hPT : P * T = value • P)
    (hi : (T - z • 1 + P).IsInvertible) (hne : value - z ≠ 0) :
    regularResolvent T P z = (1 - P) * (T - z • 1).inverse := by
  have hdecomp := (inverse_eq_pole_add_regular T P value z hPP hTP hPT hi hne).2
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    noncomm_ring [hPP]
  have hQR : (1 - P) * regularResolvent T P z = regularResolvent T P z := by
    unfold regularResolvent
    rw [← mul_assoc (1 - P), ← mul_assoc (1 - P), hQQ]
  rw [hdecomp, mul_add, mul_smul_comm, hQP, smul_zero, zero_add, hQR]

/-- The analytic regular resolvent satisfies the exact resolvent identity
even at the isolated eigenvalue: its augmented inverse is nonsingular
there and the projection removes the augmentation. -/
theorem regularResolvent_difference
    (T P : F →L[ℂ] F) (z w : ℂ) (hPP : P * P = P) (hPT : P * T = T * P)
    (hz : (T - z • 1 + P).IsInvertible) (hw : (T - w • 1 + P).IsInvertible) :
    regularResolvent T P z - regularResolvent T P w =
      (z - w) • (regularResolvent T P z * regularResolvent T P w) := by
  let Q := (1 : F →L[ℂ] F) - P
  let H := T + P
  have hQQ : Q * Q = Q := by dsimp [Q]; noncomm_ring [hPP]
  have hQH : Q * H = H * Q := by dsimp [Q, H]; noncomm_ring [hPT]
  have hzeq : H - z • 1 = T - z • 1 + P := by dsimp [H]; abel
  have hweq : H - w • 1 = T - w • 1 + P := by dsimp [H]; abel
  have hQA (c : ℂ) : Q * (H - c • 1) = (H - c • 1) * Q := by
    rw [mul_sub Q H (c • 1), sub_mul H (c • 1) Q,
      mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hQH]
  have hzr : regularResolvent T P z = Q * (H - z • 1).inverse := by
    rw [regularResolvent, ← hzeq]
    exact sandwich_eq_projected_inverse Q _ _ hQQ (hQA z)
      (by rw [hzeq]; exact hz.self_comp_inverse)
      (by rw [hzeq]; exact hz.inverse_comp_self)
  have hwr : regularResolvent T P w = Q * (H - w • 1).inverse := by
    rw [regularResolvent, ← hweq]
    exact sandwich_eq_projected_inverse Q _ _ hQQ (hQA w)
      (by rw [hweq]; exact hw.self_comp_inverse)
      (by rw [hweq]; exact hw.inverse_comp_self)
  rw [hzr, hwr]
  exact projected_inverse_difference H Q z w _ _ hQQ hQH
    (by rw [hzeq]; exact hz.self_comp_inverse)
    (by rw [hzeq]; exact hz.inverse_comp_self)
    (by rw [hweq]; exact hw.self_comp_inverse)

theorem regularResolvent_difference_norm_le
    (T P : F →L[ℂ] F) (z w : ℂ) (hPP : P * P = P) (hPT : P * T = T * P)
    (hz : (T - z • 1 + P).IsInvertible) (hw : (T - w • 1 + P).IsInvertible)
    (g : ℝ) (hg : 0 < g)
    (hrz : ‖regularResolvent T P z‖ ≤ g⁻¹) (hrw : ‖regularResolvent T P w‖ ≤ g⁻¹) :
    ‖regularResolvent T P z - regularResolvent T P w‖ ≤ ‖z - w‖ / g ^ 2 :=
  resolvent_difference_norm_le _ _ z w g hg
    (regularResolvent_difference T P z w hPP hPT hz hw) hrz hrw

end ActualRegular
end Maxwell.Defect
