import Maxwell.Continuum.WellKernelBounds

/-! Ellipticity yields an actual Coulomb majorant for the constructed
Green function; all constants remain symbolic. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Set
open scoped NNReal

theorem norm_sq_coordinates (x : Space) : ‖x‖ ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq x

theorem heatRadiusSq_lower (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (u : ℝ) (_hu : 0 < u) (hau : ∀ i, (a i : ℝ) ≤ u) (x : Space) :
    ‖x‖ ^ 2 / (4 * u) ≤ heatRadiusSq a x := by
  rw [norm_sq_coordinates, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have hi : 0 < (a i : ℝ) := (NNReal.coe_pos).mpr (pos_iff_ne_zero.mpr (ha i))
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_left (hau i) (by norm_num))

theorem heatRadiusSq_upper (a : Fin 3 → ℝ≥0)
    (l : ℝ) (hl : 0 < l) (hal : ∀ i, l ≤ (a i : ℝ)) (x : Space) :
    heatRadiusSq a x ≤ ‖x‖ ^ 2 / (4 * l) := by
  rw [norm_sq_coordinates, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_left (hal i) (by norm_num))

theorem heatPrefactor_upper (a : Fin 3 → ℝ≥0)
    (l : ℝ) (hl : 0 < l) (hal : ∀ i, l ≤ (a i : ℝ)) :
    heatPrefactor a ≤ (Real.sqrt (4 * Real.pi * l))⁻¹ ^ 3 := by
  have hprod : heatPrefactor a ≤ ∏ _ : Fin 3, (Real.sqrt (4 * Real.pi * l))⁻¹ := by
    apply Finset.prod_le_prod₀
    · intro i _
      positivity
    · intro i _
      apply inv_anti₀ (by positivity)
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hal i) (by positivity))
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod

theorem heatPrefactor_lower (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (u : ℝ) (hu : 0 < u) (hau : ∀ i, (a i : ℝ) ≤ u) :
    (Real.sqrt (4 * Real.pi * u))⁻¹ ^ 3 ≤ heatPrefactor a := by
  have hprod : (∏ _ : Fin 3, (Real.sqrt (4 * Real.pi * u))⁻¹) ≤ heatPrefactor a := by
    apply Finset.prod_le_prod₀
    · intro i _
      positivity
    · intro i _
      have hi : 0 < (a i : ℝ) := (NNReal.coe_pos).mpr (pos_iff_ne_zero.mpr (ha i))
      apply inv_anti₀ (by positivity)
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hau i) (by positivity))
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod

theorem heatRadiusSq_sqrt_lower (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (u : ℝ) (hu : 0 < u) (hau : ∀ i, (a i : ℝ) ≤ u) (x : Space) :
    ‖x‖ / (2 * Real.sqrt u) ≤ Real.sqrt (heatRadiusSq a x) := by
  have h := Real.sqrt_le_sqrt (heatRadiusSq_lower a ha u hu hau x)
  have hfour : Real.sqrt (4 : ℝ) = 2 := by
    convert Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2) using 1
    norm_num
  rwa [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hfour] at h

theorem resolventKernel_norm_bound (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (u : ℝ) (hu : 0 < u) (hau : ∀ i, (a i : ℝ) ≤ u) (x : Space) (hx : x ≠ 0) :
    resolventKernel a x ≤ (2 * heatPrefactor a * Real.sqrt Real.pi * Real.sqrt u) / ‖x‖ := by
  have hr := heatRadiusSq_sqrt_lower a ha u hu hau x
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  calc
    _ ≤ heatPrefactor a * (Real.sqrt Real.pi / Real.sqrt (heatRadiusSq a x)) :=
      resolventKernel_coulomb_bound a ha x hx
    _ ≤ heatPrefactor a * (Real.sqrt Real.pi / (‖x‖ / (2 * Real.sqrt u))) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) hr)
        (heatPrefactor_nonneg a)
    _ = _ := by field_simp

end Maxwell.Continuum.Well
