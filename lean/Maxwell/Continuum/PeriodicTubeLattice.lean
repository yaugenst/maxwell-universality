import Maxwell.Continuum.PeriodicTubeShift
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The actual placement lattice gives the stated exponent per lattice
distance. All numerical comparisons with `log 3` are certified. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

def placedDisplacement (L d : ℝ) (v : Space) : Corner.Vec :=
  (2 * L * d) • realPlacementMatrix.mulVec v.ofLp

theorem placedDisplacement_dualDistance {L d : ℝ} (hL : 0 ≤ L) (hd : 0 ≤ d)
    (v : Space) :
    dualHessianDistance (placedDisplacement L d v) =
      (2 * L * d) * ‖placementInHessianMetric v‖ := by
  rw [dualHessianDistance_eq_norm]
  have he : (WithLp.toLp 2
      (inverseSqrtHessian.mulVec (placedDisplacement L d v)) : Space) =
      (2 * L * d) • placementInHessianMetric v := by
    apply PiLp.ext
    intro j
    change (inverseSqrtHessian.mulVec (placedDisplacement L d v)) j =
      (2 * L * d) * placementInHessianMetric v j
    rw [placementInHessianMetric_apply]
    simp only [placedDisplacement, inverseSqrtHessian, realPlacementMatrix,
      Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem sum_abs_le_sqrt_three_norm (v : Space) :
    (∑ j : Fin 3, |v j|) ≤ Real.sqrt 3 * ‖v‖ := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
    (fun j => |v j|) (fun _ => (1 : ℝ))
  have hn : ‖v‖^2 = ∑ j : Fin 3, |v j|^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs]
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_ofNat, nsmul_eq_mul] at hc
  rw [← hn] at hc
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hsq : (Real.sqrt 3 * ‖v‖)^2 = 3 * ‖v‖^2 := by rw [mul_pow, hs]
  have hv : 0 ≤ ∑ j : Fin 3, |v j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  nlinarith [mul_nonneg (Real.sqrt_nonneg (3 : ℝ)) (norm_nonneg v)]

theorem tube_rate_log_three :
    Real.log 3 < 2 * (99 / 100 : ℝ)^2 / Real.sqrt 3 := by
  have hs : Real.sqrt 3 < 7 / 4 := by
    have hn := Real.sqrt_nonneg (3 : ℝ)
    have he := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith
  have hl : Real.log 3 < 11 / 10 := lt_trans Real.log_three_lt_d9 (by norm_num)
  have hsp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  apply (lt_div_iff₀ hsp).mpr
  have hm := mul_lt_mul_of_pos_right hl hsp
  nlinarith

theorem placedDisplacement_phase {L d : ℝ} (hL : 0 < L) (hd : 0 ≤ d)
    (v : Space) :
    dotProduct (optimalTubeShift L⁻¹ (placedDisplacement L d v))
      (placedDisplacement L d v) =
        (2 * (99 / 100 : ℝ)) * d * ‖placementInHessianMetric v‖ := by
  rw [optimalTubeShift_phase, placedDisplacement_dualDistance hL.le hd]
  field_simp

theorem placedDisplacement_phase_lower {L d : ℝ} (hL : 0 < L) (hd : 0 ≤ d)
    (v : Space) :
    (2 * (99 / 100 : ℝ)^2 / Real.sqrt 3) * d * (∑ j : Fin 3, |v j|) ≤
      dotProduct (optimalTubeShift L⁻¹ (placedDisplacement L d v))
        (placedDisplacement L d v) := by
  rw [placedDisplacement_phase hL hd]
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hv : (∑ j : Fin 3, |v j|) / Real.sqrt 3 ≤ ‖v‖ :=
    (div_le_iff₀ hs).mpr (by simpa only [mul_comm] using sum_abs_le_sqrt_three_norm v)
  have hmetric := (placement_metric v).1
  calc
    _ = (2 * (99 / 100 : ℝ)^2 * d) * ((∑ j : Fin 3, |v j|) / Real.sqrt 3) := by ring
    _ ≤ (2 * (99 / 100 : ℝ)^2 * d) * ‖v‖ :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = (2 * (99 / 100 : ℝ) * d) * ((99 / 100 : ℝ) * ‖v‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmetric (by positivity)

theorem placedDisplacement_phase_log_lower {L d : ℝ} (hL : 0 < L) (hd : 0 ≤ d)
    (v : Space) :
    Real.log 3 * d * (∑ j : Fin 3, |v j|) ≤
      dotProduct (optimalTubeShift L⁻¹ (placedDisplacement L d v))
        (placedDisplacement L d v) := by
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right tube_rate_log_three.le hd)
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).trans
      (placedDisplacement_phase_lower hL hd v)

theorem placedDisplacement_exponential_le {L d : ℝ} (hL : 0 < L) (hd : 0 ≤ d)
    (v : Space) :
    Real.exp (-dotProduct (optimalTubeShift L⁻¹ (placedDisplacement L d v))
      (placedDisplacement L d v)) ≤
        Real.exp (-(Real.log 3 * d * (∑ j : Fin 3, |v j|))) :=
  Real.exp_le_exp.mpr (neg_le_neg (placedDisplacement_phase_log_lower hL hd v))

end Maxwell.Continuum.PeriodicBand
