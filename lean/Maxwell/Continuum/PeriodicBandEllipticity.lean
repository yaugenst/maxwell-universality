import Maxwell.Continuum.PeriodicBandQuadratic
import Mathlib.Analysis.Real.Pi.Bounds

/-! Uniform positive definiteness of the actual band Hessian. The estimate
is obtained from the exact corner inverse and the proved self-energy error. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber CornerBridge

theorem dot_self_nonneg (t : Corner.Vec) : 0 ≤ dotProduct t t :=
  Finset.sum_nonneg (fun j _ => mul_self_nonneg (t j))

theorem coordinate_sq_le_dot (t : Corner.Vec) (j : Fin 3) : (t j)^2 ≤ dotProduct t t := by
  simpa only [dotProduct, pow_two] using
    (Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => mul_self_nonneg (t k))
      (Finset.mem_univ j))

theorem bandQuadratic_comparison (t : Corner.Vec) :
    ‖bandQuadratic (realMomentum t) - (cornerQuadratic t : ℂ)‖ ≤
      ((2 : ℝ)^34 * backgroundAmplitude) * dotProduct t t := by
  by_cases ht : t = 0
  · subst t
    have hz : realMomentum (0 : Corner.Vec) = 0 := by funext j; simp [realMomentum]
    simp [hz, bandQuadratic_zero, cornerQuadratic, dotProduct]
  have hS : 0 < dotProduct t t :=
    lt_of_le_of_ne (dot_self_nonneg t) (Ne.symm (mt dotProduct_self_eq_zero.mp ht))
  let a : ℝ := Real.sqrt (dotProduct t t)
  have ha : 0 < a := Real.sqrt_pos.mpr hS
  have ha2 : a ^ 2 = dotProduct t t := Real.sq_sqrt hS.le
  let v : Corner.Vec := a⁻¹ • t
  have hv : ∀ j, |v j| ≤ 1 := by
    intro j
    have htj : |t j| ≤ a := by
      have habs : |t j| ^ 2 = (t j)^2 := sq_abs (t j)
      nlinarith [coordinate_sq_le_dot t j, abs_nonneg (t j)]
    change |a⁻¹ * t j| ≤ 1
    rw [abs_mul, abs_inv, abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left htj (inv_nonneg.mpr ha.le)).trans_eq (inv_mul_cancel₀ ha.ne')
  have hrec : t = a • v := by
    dsimp only [v]
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have herr := bandQuadratic_unit_comparison v hv
  have heq : bandQuadratic (realMomentum t) - (cornerQuadratic t : ℂ) =
      (a : ℂ)^2 * (bandQuadratic (realMomentum v) - (cornerQuadratic v : ℂ)) := by
    nth_rw 1 [hrec]
    nth_rw 1 [hrec]
    rw [realMomentum_smul, bandQuadratic_smul, cornerQuadratic_smul]
    push_cast
    ring
  rw [heq, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  calc
    _ ≤ a ^ 2 * ((2 : ℝ)^34 * backgroundAmplitude) :=
      mul_le_mul_of_nonneg_left herr (sq_nonneg a)
    _ = ((2 : ℝ)^34 * backgroundAmplitude) * dotProduct t t := by rw [ha2]; ring

theorem bandQuadratic_real_comparison (t : Corner.Vec) :
    |(bandQuadratic (realMomentum t)).re - cornerQuadratic t| ≤
      ((2 : ℝ)^34 * backgroundAmplitude) * dotProduct t t := by
  have h := Complex.abs_re_le_norm (bandQuadratic (realMomentum t) - (cornerQuadratic t : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at h
  exact h.trans (bandQuadratic_comparison t)

/-- The actual scaled Hessian coefficient obeys the paper's numerical margins. -/
theorem bandQuadratic_bounds (t : Corner.Vec) :
    (1 / 2 : ℝ) * dotProduct t t ≤ (bandQuadratic (realMomentum t)).re ∧
      (bandQuadratic (realMomentum t)).re ≤ 256 * dotProduct t t := by
  have herr := abs_le.mp (bandQuadratic_real_comparison t)
  have hcorner := cornerQuadratic_bounds t
  have hsmall : (2 : ℝ)^34 * backgroundAmplitude ≤ 1 / 100 := by
    norm_num [backgroundAmplitude]
  have hS := dot_self_nonneg t
  have herr' := mul_le_mul_of_nonneg_right hsmall hS
  have hlo : (1 / 2 : ℝ) + 1 / 100 ≤ Real.pi ^ 2 / 14 := by
    nlinarith [Real.pi_gt_three]
  have hhi : 20 * Real.pi ^ 2 + 1 / 100 ≤ 256 := by
    nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have hlo' := mul_le_mul_of_nonneg_right hlo hS
  have hhi' := mul_le_mul_of_nonneg_right hhi hS
  constructor <;> nlinarith

end Maxwell.Continuum.PeriodicBand
