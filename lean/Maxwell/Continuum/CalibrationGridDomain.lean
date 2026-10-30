import Maxwell.Continuum.CalibrationGridCutoff
import Maxwell.Continuum.CalibrationSampledSchur

/-! A rational support test for the sampled inverse. Every nonzero
literal cutoff sample passes; every passing sample lies in the proved
physical inverse chart. No test of a transcendental cutoff is needed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open FreeFiber Auxiliary PeriodicBand

def activeGrid (r : Fin 3 → ℚ) : Prop := ∀ j, |r j| ≤ rationalSmallRadius

instance (r : Fin 3 → ℚ) : Decidable (activeGrid r) :=
  inferInstanceAs (Decidable (∀ j : Fin 3, |r j| ≤ rationalSmallRadius))

def gridMomentum (r : Fin 3 → ℚ) : Corner.Vec := fun j => Real.pi*(r j : ℝ)

theorem activeGrid_cast {r : Fin 3 → ℚ} (hr : activeGrid r) (j : Fin 3) :
    |(r j : ℝ)| ≤ smallRadius := by
  rw [← rationalSmallRadius_cast]
  exact_mod_cast hr j

theorem activeGrid_direction {r : Fin 3 → ℚ} (hr : activeGrid r) :
    ∀ j, |(r j : ℝ)| ≤ 1/16 := by
  intro j
  exact (activeGrid_cast hr j).trans (by norm_num [smallRadius,backgroundAmplitude])

theorem activeGrid_momentum {r : Fin 3 → ℚ} (hr : activeGrid r) :
    ‖realMomentum (gridMomentum r)‖ ≤ 4*smallRadius := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) smallRadius_pos.le)).mpr
  intro j
  simp only [realMomentum,gridMomentum,Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_pos Real.pi_pos]
  have h := activeGrid_cast hr j
  nlinarith [Real.pi_lt_four,Real.pi_pos,smallRadius_pos]

theorem cutoff_zero_of_inactive {r : Fin 3 → ℚ} (hr : ¬activeGrid r) :
    cutoff (WithLp.toLp 2 (gridMomentum r)) = 0 := by
  by_contra hn
  apply hr
  intro j
  have hc := cutoff_ne_zero_coordinate_lt hn j
  change |Real.pi*(r j : ℝ)| < 2*smallRadius at hc
  rw [abs_mul,abs_of_pos Real.pi_pos] at hc
  have hb : |(r j : ℝ)| ≤ smallRadius := by
    nlinarith [Real.pi_gt_three,smallRadius_pos,abs_nonneg (r j : ℝ)]
  rw [← rationalSmallRadius_cast] at hb
  exact_mod_cast hb

theorem sampled_totalEnergy_bounds {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4*smallRadius) :
    7 ≤ z+σ+7 ∧ z+σ+7 ≤ 8 := by
  have he := sampledEnergy_norm D hσ0 hσ q hq
  have hp := energy_perturbation_norm_le (sampledScaledEnergy z σ) he
  have hb := (Complex.abs_re_le_norm ((backgroundAmplitude : ℂ)*sampledScaledEnergy z σ)).trans hp
  have hid : (totalEnergy (sampledScaledEnergy z σ)).re = z+σ+7 := by
    rw [sampledScaledEnergy,totalEnergy_scaledEnergy]
    rfl
  have heq : z+σ+7-3*Real.pi^2/4 =
      ((backgroundAmplitude : ℂ)*sampledScaledEnergy z σ).re := by
    rw [← hid]
    simp only [totalEnergy,Complex.add_re,Complex.ofReal_re,add_sub_cancel_left]
  rw [← heq] at hb
  have ha := abs_le.mp hb
  constructor <;> nlinarith [Real.pi_gt_d2,Real.pi_lt_d2,Real.pi_pos]

#print axioms activeGrid_momentum
#print axioms cutoff_zero_of_inactive
#print axioms sampled_totalEnergy_bounds

end Maxwell.Continuum.Calibration
