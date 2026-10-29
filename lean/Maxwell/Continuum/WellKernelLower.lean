import Maxwell.Continuum.WellKernelBounds

/-! A positive lower bound is extracted from a literal interval of the
heat mixture. This is the minorization needed by the Perron argument. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Set
open scoped NNReal

theorem heatMixture_interval_lower (a : Fin 3 → ℝ≥0) (x : Space)
    (τ M : ℝ) (hτ : 0 < τ) (hR : heatRadiusSq a x ≤ M)
    (t : ℝ) (ht : t ∈ Icc τ (2 * τ)) :
    heatPrefactor a * (2 * τ) ^ (-3 / 2 : ℝ) * Real.exp (-2 * τ - M / τ) ≤
      Real.exp (-t) * heatKernel a t x := by
  have htpos : 0 < t := hτ.trans_le ht.1
  have hM : 0 ≤ M := (heatRadiusSq_nonneg a x).trans hR
  have hfrac : heatRadiusSq a x / t ≤ M / τ :=
    (div_le_div_of_nonneg_right hR htpos.le).trans
      (div_le_div_of_nonneg_left hM hτ ht.1)
  have htime : (2 * τ) ^ (-3 / 2 : ℝ) ≤ t ^ (-3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos htpos ht.2 (by norm_num)
  have hexp : Real.exp (-2 * τ - M / τ) ≤
      Real.exp (-t - heatRadiusSq a x / t) := by
    apply Real.exp_le_exp.mpr
    linarith [ht.2]
  rw [heatKernel_literal a t htpos x, inverseTimeGaussian]
  calc
    _ ≤ heatPrefactor a * t ^ (-3 / 2 : ℝ) * Real.exp (-t - heatRadiusSq a x / t) :=
      mul_le_mul (mul_le_mul_of_nonneg_left htime (heatPrefactor_nonneg a)) hexp
        (Real.exp_pos _).le (mul_nonneg (heatPrefactor_nonneg a) (Real.rpow_nonneg htpos.le _))
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add]
      simp only [neg_div]
      ring

theorem resolventKernel_interval_lower (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (x : Space) (hx : x ≠ 0) (τ M : ℝ) (hτ : 0 < τ) (hR : heatRadiusSq a x ≤ M) :
    τ * heatPrefactor a * (2 * τ) ^ (-3 / 2 : ℝ) * Real.exp (-2 * τ - M / τ) ≤
      resolventKernel a x := by
  have hsub : Icc τ (2 * τ) ⊆ Ioi (0 : ℝ) := fun _ ht => hτ.trans_le ht.1
  have hfi := heatMixture_pointwise_integrable a ha x hx
  let C : ℝ := heatPrefactor a * (2 * τ) ^ (-3 / 2 : ℝ) * Real.exp (-2 * τ - M / τ)
  have hc : IntegrableOn (fun _ : ℝ => C) (Icc τ (2 * τ)) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have h₁ : (∫ t : ℝ in Icc τ (2 * τ), C) ≤
      ∫ t : ℝ in Icc τ (2 * τ), Real.exp (-t) * heatKernel a t x := by
    apply setIntegral_mono_on hc (hfi.mono_set hsub) measurableSet_Icc
    intro t ht
    exact heatMixture_interval_lower a x τ M hτ hR t ht
  have h₂ : (∫ t : ℝ in Icc τ (2 * τ), Real.exp (-t) * heatKernel a t x) ≤
      resolventKernel a x := by
    apply setIntegral_mono_set hfi
    · exact Filter.Eventually.of_forall (fun t => mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg a t x))
    · exact Filter.Eventually.of_forall (fun _ ht => hsub ht)
  rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * τ - τ)] at h₁
  have he : (2 * τ - τ) * C =
      τ * heatPrefactor a * (2 * τ) ^ (-3 / 2 : ℝ) * Real.exp (-2 * τ - M / τ) := by
    dsimp [C]
    ring
  rw [he] at h₁
  exact h₁.trans h₂

theorem resolventKernel_pos (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (x : Space) (hx : x ≠ 0) : 0 < resolventKernel a x := by
  have h := resolventKernel_interval_lower a ha x hx 1 (heatRadiusSq a x) (by norm_num) le_rfl
  apply lt_of_lt_of_le _ h
  have hp := heatPrefactor_pos a ha
  positivity

end Maxwell.Continuum.Well
