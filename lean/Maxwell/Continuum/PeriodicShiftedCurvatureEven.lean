import Maxwell.Continuum.PeriodicShiftedCurvatureBasic

/-! Even symmetrization of the actual remainder gives a quadratic
difference estimate around any sufficiently small complex center. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Set Metric Filter
open scoped Topology

attribute [local irreducible] physicalRemainder

def symmetrizedRemainder (a b : Momentum) (ζ : ℂ) : ℂ :=
  (physicalRemainder (ζ • a + b) + physicalRemainder ((-ζ) • a + b)) / 2

theorem small_center_line_norm (a b : Momentum) (ha : ‖a‖ = 1)
    (hb : ‖b‖ ≤ smallRadius) {ζ : ℂ} (hζ : ‖ζ‖ < 8 * smallRadius) :
    ‖ζ • a + b‖ ≤ 9 * smallRadius := by
  calc
    _ ≤ ‖ζ • a‖ + ‖b‖ := norm_add_le _ _
    _ = ‖ζ‖ + ‖b‖ := by rw [norm_smul, ha, mul_one]
    _ ≤ _ := by linarith

theorem nine_smallRadius_le_half : 9 * smallRadius ≤ analyticRadius / 2 := by
  norm_num [smallRadius, analyticRadius, backgroundAmplitude]

theorem small_center_line_chart (a b : Momentum) (ha : ‖a‖ = 1)
    (hb : ‖b‖ ≤ smallRadius) {ζ : ℂ} (hζ : ‖ζ‖ < 8 * smallRadius) :
    ζ • a + b ∈ physicalChart := by
  intro j
  exact ((norm_le_pi_norm _ j).trans
    ((small_center_line_norm a b ha hb hζ).trans nine_smallRadius_le_half)).trans_lt
      (by linarith [analyticRadius_pos])

theorem symmetrizedRemainder_analytic (a b : Momentum) (ha : ‖a‖ = 1)
    (hb : ‖b‖ ≤ smallRadius) :
    AnalyticOnNhd ℂ (symmetrizedRemainder a b) (ball 0 (8 * smallRadius)) := by
  intro ζ hζ
  have hz : ‖ζ‖ < 8 * smallRadius := by simpa using hζ
  have hp := (physicalRemainder_analyticAt (small_center_line_chart a b ha hb hz)).comp
    (f := fun ξ : ℂ => ξ • a + b) ((analyticAt_id.smul analyticAt_const).add analyticAt_const)
  have hn := (physicalRemainder_analyticAt
    (small_center_line_chart a b ha hb (ζ := -ζ) (by simpa using hz))).comp
      (f := fun ξ : ℂ => (-ξ) • a + b)
      ((analyticAt_id.neg.smul analyticAt_const).add analyticAt_const)
  exact (hp.add hn).div_const

theorem symmetrizedRemainder_even (a b : Momentum) :
    (fun ζ => symmetrizedRemainder a b (-ζ)) =ᶠ[𝓝 0] symmetrizedRemainder a b :=
  Filter.Eventually.of_forall (fun ζ => by simp only [symmetrizedRemainder, neg_neg, add_comm])

theorem symmetrizedRemainder_norm (a b : Momentum) (ha : ‖a‖ = 1)
    (hb : ‖b‖ ≤ smallRadius) {ζ : ℂ} (hζ : ‖ζ‖ < 8 * smallRadius) :
    ‖symmetrizedRemainder a b ζ‖ ≤ quarticConstant * (9 * smallRadius)^4 := by
  have hc := quarticConstant_nonneg
  have hbound (ξ : ℂ) (hξ : ‖ξ‖ < 8 * smallRadius) :
      ‖physicalRemainder (ξ • a + b)‖ ≤ quarticConstant * (9 * smallRadius)^4 := by
    have hn := small_center_line_norm a b ha hb hξ
    exact (physicalRemainder_norm_le (hn.trans nine_smallRadius_le_half)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 4) hc)
  unfold symmetrizedRemainder
  calc
    _ = ‖physicalRemainder (ζ • a + b) + physicalRemainder ((-ζ) • a + b)‖ / 2 := by
      rw [norm_div]
      norm_num
    _ ≤ (quarticConstant * (9 * smallRadius)^4 + quarticConstant * (9 * smallRadius)^4) / 2 :=
      div_le_div_of_nonneg_right ((norm_add_le _ _).trans
        (add_le_add (hbound ζ hζ) (hbound (-ζ) (by simpa using hζ)))) (by norm_num)
    _ = _ := by ring

theorem symmetrizedRemainder_zero (a b : Momentum) :
    symmetrizedRemainder a b 0 = physicalRemainder b := by
  simp only [symmetrizedRemainder, neg_zero, zero_smul, zero_add]
  ring

theorem symmetrizedRemainder_difference (a b : Momentum) (ha : ‖a‖ = 1)
    (hb : ‖b‖ ≤ smallRadius) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 4 * smallRadius) :
    ‖symmetrizedRemainder a b ζ - physicalRemainder b‖ ≤
      (2 * (quarticConstant * (9 * smallRadius)^4) / (8 * smallRadius)^2) * ‖ζ‖^2 := by
  have he := EvenTaylor.quadratic_difference_bound
    (symmetrizedRemainder_analytic a b ha hb)
    (fun ξ hξ => symmetrizedRemainder_norm a b ha hb (by simpa using hξ))
    (mul_pos (by norm_num) smallRadius_pos)
    (mul_nonneg quarticConstant_nonneg
      (pow_nonneg (mul_nonneg (by norm_num) smallRadius_pos.le) 4))
    (symmetrizedRemainder_even a b) (by linarith : ‖ζ‖ ≤ (8 * smallRadius) / 2)
  rwa [symmetrizedRemainder_zero] at he

end Maxwell.Continuum.PeriodicBand
