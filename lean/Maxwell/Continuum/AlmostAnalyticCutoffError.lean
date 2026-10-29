import Maxwell.Continuum.AlmostAnalyticCutoff
import Maxwell.Continuum.AlmostAnalyticOptimization
import Maxwell.Continuum.MasterConstants

/-! The paper's exponentially small Cauchy--Riemann defect for the
literal compact Bloch cutoff at the symbolic master length. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.AlmostAnalytic

open Complex PeriodicBand MasterConstants

def cutoffOrder (β : Space) : ℕ :=
  truncationOrder (((2 : ℝ)^16 / smallRadius) * ‖β‖)

theorem cutoff_scale : (2 : ℝ)^16 / smallRadius = (2 : ℝ)^156 := by
  norm_num [smallRadius, FreeFiber.backgroundAmplitude]

theorem cutoffOrder_ge_length {L : ℝ} (hL : Ls ≤ L) {β : Space}
    (hβ : ‖β‖ ≤ L⁻¹) (hβ0 : β ≠ 0) :
    ⌊L/(2 : ℝ)^158⌋₊ ≤ cutoffOrder β := by
  have hp : 0 < L := length_pos hL
  have hr : 0 < ‖β‖ := norm_pos_iff.mpr hβ0
  have hrL : ‖β‖ * L ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hβ hp.le
    simpa only [inv_mul_cancel₀ hp.ne'] using hm
  unfold cutoffOrder truncationOrder
  rw [cutoff_scale]
  apply Nat.floor_mono
  rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
  have he : (L/(2 : ℝ)^158) * (4*((2 : ℝ)^156*‖β‖)) = ‖β‖*L := by ring
  rwa [he]

theorem cutoffOrder_pos {L : ℝ} (hL : Ls ≤ L) {β : Space}
    (hβ : ‖β‖ ≤ L⁻¹) (hβ0 : β ≠ 0) : 1 ≤ cutoffOrder β := by
  apply le_trans _ (cutoffOrder_ge_length hL hβ hβ0)
  apply (Nat.one_le_floor_iff _).mpr
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [one_mul] using
    (power_le_Ls (n := 158) (by have := exponent_large; omega)).trans hL

theorem cutoffTaylor_error_small {L : ℝ} (hL : Ls ≤ L) {β : Space}
    (hβ : ‖β‖ ≤ L⁻¹) (hβ0 : β ≠ 0) (q : Space) {s : ℝ} (hs : |s| ≤ 1) :
    ‖deriv (fun t : ℝ => cutoffTaylor (cutoffOrder β) smallRadius q β t) s -
      I * deriv (fun t : ℝ => cutoffTaylor (cutoffOrder β) smallRadius (q+t • β) β s) 0‖ ≤
      (2 : ℝ)^46 * Real.exp (-cs*L) := by
  let t := ((2 : ℝ)^16 / smallRadius) * ‖β‖
  have ht : 0 < t := mul_pos (div_pos (by positivity) smallRadius_pos) (norm_pos_iff.mpr hβ0)
  have hts : t ≤ 1/4 := by
    have hb : ‖β‖ ≤ 1/(2 : ℝ)^1024 := hβ.trans (inverse_length_le_1024 hL)
    dsimp only [t]
    rw [cutoff_scale]
    exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans (by norm_num)
  have hbound := cutoffTaylor_defect_bound (cutoffOrder β) smallRadius smallRadius_pos q β hs
  have he := mul_le_mul_of_nonneg_left (truncation_remainder_exp ht hts)
    (show (0 : ℝ) ≤ 2^45 by positivity)
  have herror : ‖deriv (fun t : ℝ => cutoffTaylor (cutoffOrder β) smallRadius q β t) s -
      I * deriv (fun t : ℝ => cutoffTaylor (cutoffOrder β) smallRadius (q+t • β) β s) 0‖ ≤
      (2 : ℝ)^46 * Real.exp (-1/(8*t)) := by
    apply hbound.trans
    convert he using 1 <;> dsimp only [cutoffOrder, t] <;> ring
  have hp : 0 < L := length_pos hL
  have hrL : ‖β‖ * L ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hβ hp.le
    simpa only [inv_mul_cancel₀ hp.ne'] using hm
  have hl : L/(2 : ℝ)^159 ≤ 1/(8*t) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have he : (L/(2 : ℝ)^159)*(8*t) = ‖β‖*L := by
      dsimp only [t]
      rw [cutoff_scale]
      ring
    rwa [he]
  have hc : cs * L ≤ L/(2 : ℝ)^159 := by
    have hn : cs ≤ 1/(2 : ℝ)^159 := by norm_num [cs]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using mul_le_mul_of_nonneg_right hn hp.le
  apply herror.trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
  simpa only [neg_div, neg_mul] using neg_le_neg (hc.trans hl)

theorem cutoffTaylor_error_exp {L : ℝ} (hL : Ls ≤ L) {β : Space}
    (hβ : ‖β‖ ≤ L⁻¹) (hβ0 : β ≠ 0) (q : Space) {s : ℝ} (hs : |s| ≤ 1) :
    ‖deriv (fun t : ℝ => cutoffTaylor (cutoffOrder β) smallRadius q β t) s -
      I * deriv (fun t : ℝ => cutoffTaylor (cutoffOrder β) smallRadius (q+t • β) β s) 0‖ ≤
      Cs * Real.exp (-cs*L) :=
  (cutoffTaylor_error_small hL hβ hβ0 q hs).trans
    (mul_le_mul_of_nonneg_right
      (fixed_power_le_Cs (by have := exponent_large; omega)) (Real.exp_pos _).le)

#print axioms cutoffTaylor_error_exp

end Maxwell.Continuum.AlmostAnalytic
