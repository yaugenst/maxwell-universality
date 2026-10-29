import Maxwell.Defect.Radial
import Maxwell.Defect.KernelBounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Abel

/-! Local compressed-band integrals with explicit integrable remainders. -/

open MeasureTheory Set Real

namespace Maxwell.Defect

abbrev Momentum := EuclideanSpace ℝ (Fin 3)

section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem local_band_integrable (B : Momentum → F) (d : Momentum → ℝ)
    (W : F) {R c M ξ : ℝ} (hc : 0 < c) (hξ : 0 ≤ ξ)
    (hBm : AEStronglyMeasurable B (volume.restrict (Metric.ball 0 R)))
    (hdm : Measurable d)
    (hd : ∀ q ∈ Metric.ball 0 R, q ≠ 0 → c * ‖q‖ ^ 2 ≤ d q)
    (hB : ∀ q ∈ Metric.ball 0 R, ‖B q - W‖ ≤ M * ‖q‖ ^ 2) :
    IntegrableOn (fun q => (d q + ξ)⁻¹ • B q) (Metric.ball 0 R) := by
  have hconst : IntegrableOn (fun _ : Momentum => M / c) (Metric.ball 0 R) :=
    integrableOn_const
  have hmajor := ((inverse_square_integrable_ball R).const_mul (‖W‖ / c)).add hconst
  apply hmajor.mono' (((hdm.add_const ξ).inv.aestronglyMeasurable).smul hBm)
  have hne : ∀ᵐ q : Momentum, q ≠ 0 := by simp [ae_iff]
  filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne] with q hq hq0
  have hr : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hdq : 0 < d q + ξ := by nlinarith [hd q hq hq0, sq_pos_of_pos hr]
  have hBn : ‖B q‖ ≤ ‖W‖ + M * ‖q‖ ^ 2 := by
    have ht := norm_le_norm_add_norm_sub W (B q)
    rw [norm_sub_rev W (B q)] at ht
    linarith [hB q hq]
  change ‖(d q + ξ)⁻¹ • B q‖ ≤ ‖W‖ / c * (1 / ‖q‖ ^ 2) + M / c
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdq)]
  calc
    (d q + ξ)⁻¹ * ‖B q‖ ≤ (c * ‖q‖ ^ 2)⁻¹ * (‖W‖ + M * ‖q‖ ^ 2) := by
      gcongr
      nlinarith [hd q hq hq0]
    _ = ‖W‖ / c * (1 / ‖q‖ ^ 2) + M / c := by field_simp

theorem local_band_difference (B : Momentum → F) (d : Momentum → ℝ)
    (W : F) {R c M ξ : ℝ} (hc : 0 < c) (hξ : 0 ≤ ξ)
    (hBm : AEStronglyMeasurable B (volume.restrict (Metric.ball 0 R)))
    (hdm : Measurable d)
    (hd : ∀ q ∈ Metric.ball 0 R, q ≠ 0 → c * ‖q‖ ^ 2 ≤ d q)
    (hB : ∀ q ∈ Metric.ball 0 R, ‖B q - W‖ ≤ M * ‖q‖ ^ 2) :
    (∫ q in Metric.ball 0 R, (d q)⁻¹ • B q) -
      (∫ q in Metric.ball 0 R, (d q + ξ)⁻¹ • B q) =
        ∫ q in Metric.ball 0 R, resolventDifference ξ (d q) • B q := by
  have hi0 := local_band_integrable B d W hc (show (0 : ℝ) ≤ 0 by rfl) hBm hdm hd hB
  simp only [add_zero] at hi0
  rw [← integral_sub hi0 (local_band_integrable B d W hc hξ hBm hdm hd hB)]
  apply integral_congr_ae
  have hne : ∀ᵐ q : Momentum, q ≠ 0 := by simp [ae_iff]
  filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne] with q hq hq0
  have hr : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hdq : 0 < d q := lt_of_lt_of_le (by positivity) (hd q hq hq0)
  have hdqx : 0 < d q + ξ := by positivity
  rw [← sub_smul]
  congr 1
  unfold resolventDifference
  field_simp
  ring

theorem local_resolvent_difference_integrable (B : Momentum → F) (d : Momentum → ℝ)
    (W : F) {R c M ξ : ℝ} (hc : 0 < c) (hξ : 0 ≤ ξ)
    (hBm : AEStronglyMeasurable B (volume.restrict (Metric.ball 0 R)))
    (hdm : Measurable d)
    (hd : ∀ q ∈ Metric.ball 0 R, q ≠ 0 → c * ‖q‖ ^ 2 ≤ d q)
    (hB : ∀ q ∈ Metric.ball 0 R, ‖B q - W‖ ≤ M * ‖q‖ ^ 2) :
    IntegrableOn (fun q => resolventDifference ξ (d q) • B q) (Metric.ball 0 R) := by
  have hi0 := local_band_integrable B d W hc (show (0 : ℝ) ≤ 0 by rfl) hBm hdm hd hB
  simp only [add_zero] at hi0
  apply (hi0.sub (local_band_integrable B d W hc hξ hBm hdm hd hB)).congr
  have hne : ∀ᵐ q : Momentum, q ≠ 0 := by simp [ae_iff]
  filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne] with q hq hq0
  have hr : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hdq : 0 < d q := lt_of_lt_of_le (by positivity) (hd q hq hq0)
  have hdqx : 0 < d q + ξ := by positivity
  change (d q)⁻¹ • B q - (d q + ξ)⁻¹ • B q = resolventDifference ξ (d q) • B q
  rw [← sub_smul]
  congr 1
  unfold resolventDifference
  field_simp
  ring

theorem combined_local_error_bound {ξ d e c r M_B M_d : ℝ} {B W : F}
    (hξ : 0 ≤ ξ) (hc : 0 < c) (hr : 0 < r) (hMB : 0 ≤ M_B)
    (hd : c * r ^ 2 ≤ d) (he : c * r ^ 2 ≤ e)
    (hdisp : |d - e| ≤ M_d * r ^ 4) (hnum : ‖B - W‖ ≤ M_B * r ^ 2) :
    ‖resolventDifference ξ d • B - resolventDifference ξ e • W‖ ≤
      (M_B / c ^ 2 + 2 * M_d * ‖W‖ / c ^ 3) * ξ / r ^ 2 := by
  have hid : resolventDifference ξ d • B - resolventDifference ξ e • W =
      resolventDifference ξ d • (B - W) +
        (resolventDifference ξ d - resolventDifference ξ e) • W := by
    rw [smul_sub, sub_smul]
    abel
  rw [hid]
  apply (norm_add_le _ _).trans
  have hb := numerator_replacement_bound hξ hc hr hMB hd hnum
  have hdif := dispersion_replacement_bound hξ hc hr hd he hdisp
  simp only [norm_smul, Real.norm_eq_abs] at hb ⊢
  have hw := mul_le_mul_of_nonneg_right hdif (norm_nonneg W)
  calc
    _ ≤ M_B * ξ / (c ^ 2 * r ^ 2) + (2 * M_d * ξ / (c ^ 3 * r ^ 2)) * ‖W‖ :=
      add_le_add hb hw
    _ = (M_B / c ^ 2 + 2 * M_d * ‖W‖ / c ^ 3) * ξ / r ^ 2 := by ring

theorem quadratic_kernel_integral (L : Momentum ≃L[ℝ] Momentum)
    {ξ : ℝ} (hξ : 0 < ξ) :
    (∫ q : Momentum, resolventDifference ξ (‖L q‖ ^ 2)) =
      2 * Real.pi ^ 2 * Real.sqrt ξ / |LinearMap.det L.toLinearEquiv.toLinearMap| := by
  have hnorm := anisotropic_radial_sqrt L hξ
  apply (div_left_inj' (by positivity : (2 * Real.pi) ^ 3 ≠ 0)).mp
  unfold resolventDifference
  rw [hnorm]
  field_simp
  ring

theorem quadratic_kernel_integrable (L : Momentum ≃L[ℝ] Momentum)
    {ξ : ℝ} (hξ : 0 < ξ) :
    Integrable (fun q : Momentum => resolventDifference ξ (‖L q‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [quadratic_kernel_integral L hξ]
  have hd := L.toLinearEquiv.isUnit_det'.ne_zero
  have hs := Real.sqrt_pos.mpr hξ
  positivity

/-- The actual local compressed-band square-root expansion, with explicit
linear-in-ξ remainder. The premises are the local dispersion/numerator
chart; the limiting inverse and its integrability are proved above. -/
theorem local_compressed_sqrt_expansion [CompleteSpace F]
    (B : Momentum → F) (d : Momentum → ℝ) (W : F)
    (L : Momentum ≃L[ℝ] Momentum) {R c M_B M_d ξ : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hMB : 0 ≤ M_B) (hξ : 0 < ξ)
    (hBm : AEStronglyMeasurable B (volume.restrict (Metric.ball 0 R)))
    (hdm : Measurable d)
    (hd : ∀ q ∈ Metric.ball 0 R, q ≠ 0 → c * ‖q‖ ^ 2 ≤ d q)
    (hQ : ∀ q, c * ‖q‖ ^ 2 ≤ ‖L q‖ ^ 2)
    (hdisp : ∀ q ∈ Metric.ball 0 R, |d q - ‖L q‖ ^ 2| ≤ M_d * ‖q‖ ^ 4)
    (hB : ∀ q ∈ Metric.ball 0 R, ‖B q - W‖ ≤ M_B * ‖q‖ ^ 2) :
    ‖(∫ q in Metric.ball 0 R, (d q)⁻¹ • B q) -
      (∫ q in Metric.ball 0 R, (d q + ξ)⁻¹ • B q) -
        (2 * Real.pi ^ 2 * Real.sqrt ξ /
          |LinearMap.det L.toLinearEquiv.toLinearMap|) • W‖ ≤
      (4 * Real.pi * R * (M_B / c ^ 2 + 2 * M_d * ‖W‖ / c ^ 3) +
        4 * Real.pi / R * (‖W‖ / c ^ 2)) * ξ := by
  let localError : Momentum → F := fun q =>
    resolventDifference ξ (d q) • B q - resolventDifference ξ (‖L q‖ ^ 2) • W
  have hiD := local_resolvent_difference_integrable B d W hc hξ.le hBm hdm hd hB
  have hiQ := (quadratic_kernel_integrable L hξ).smul_const W
  have htotal : (∫ q : Momentum, resolventDifference ξ (‖L q‖ ^ 2) • W) =
      (2 * Real.pi ^ 2 * Real.sqrt ξ /
        |LinearMap.det L.toLinearEquiv.toLinearMap|) • W := by
    rw [integral_smul_const, quadratic_kernel_integral L hξ]
  have hin : ‖∫ q in Metric.ball 0 R, localError q‖ ≤
      4 * Real.pi * R * (M_B / c ^ 2 + 2 * M_d * ‖W‖ / c ^ 3) * ξ := by
    apply norm_integral_ball_error localError hR
    intro q hq hq0
    exact combined_local_error_bound hξ.le hc (norm_pos_iff.mpr hq0) hMB
      (hd q hq hq0) (hQ q) (hdisp q hq) (hB q hq)
  have hout : ‖∫ q in (Metric.ball 0 R)ᶜ, resolventDifference ξ (‖L q‖ ^ 2) • W‖ ≤
      4 * Real.pi / R * (‖W‖ / c ^ 2) * ξ := by
    apply norm_integral_exterior_error _ hR
    intro q hq
    have hr : 0 < ‖q‖ := by
      have hlarge : R ≤ ‖q‖ := by simpa [Metric.mem_ball, dist_zero_right] using hq
      exact lt_of_lt_of_le hR hlarge
    have hL : 0 < ‖L q‖ ^ 2 := lt_of_lt_of_le (by positivity) (hQ q)
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (resolventDifference_nonneg hξ.le hL)]
    calc
      _ ≤ (ξ / (‖L q‖ ^ 2) ^ 2) * ‖W‖ :=
        mul_le_mul_of_nonneg_right (resolventDifference_le hξ.le hL) (norm_nonneg W)
      _ ≤ (ξ / (c * ‖q‖ ^ 2) ^ 2) * ‖W‖ := by gcongr; exact hQ q
      _ = (‖W‖ / c ^ 2) * ξ / ‖q‖ ^ 4 := by ring
  have hid : (∫ q in Metric.ball 0 R, (d q)⁻¹ • B q) -
      (∫ q in Metric.ball 0 R, (d q + ξ)⁻¹ • B q) -
        (2 * Real.pi ^ 2 * Real.sqrt ξ /
          |LinearMap.det L.toLinearEquiv.toLinearMap|) • W =
      (∫ q in Metric.ball 0 R, localError q) -
        ∫ q in (Metric.ball 0 R)ᶜ, resolventDifference ξ (‖L q‖ ^ 2) • W := by
    rw [local_band_difference B d W hc hξ.le hBm hdm hd hB, ← htotal,
      ← integral_add_compl measurableSet_ball hiQ]
    change _ = (∫ q in Metric.ball 0 R,
      resolventDifference ξ (d q) • B q - resolventDifference ξ (‖L q‖ ^ 2) • W) - _
    rw [integral_sub hiD hiQ.integrableOn]
    abel
  rw [hid]
  apply (norm_sub_le _ _).trans
  have hsum := add_le_add hin hout
  convert hsum using 1; ring

theorem separated_band_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (B : X → F) (d : X → ℝ) {g : ℝ} (hg : 0 < g)
    (hB : Integrable B μ) (hdm : Measurable d) (hgap : ∀ᵐ x ∂μ, g ≤ |d x|) :
    Integrable (fun x => (d x)⁻¹ • B x) μ := by
  apply (hB.norm.const_mul g⁻¹).mono' (hdm.inv.aestronglyMeasurable.smul hB.aestronglyMeasurable)
  filter_upwards [hgap] with x hx
  change ‖(d x)⁻¹ • B x‖ ≤ g⁻¹ * ‖B x‖
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  gcongr

/-- The complementary Bloch contribution is `O(ξ)` with an explicit
constant; signed lower bands are included. -/
theorem separated_band_difference_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (B : X → F) (d : X → ℝ) {g ξ : ℝ} (hg : 0 < g)
    (hξ : 0 ≤ ξ) (hsmall : ξ ≤ g / 2)
    (hB : Integrable B μ) (hdm : Measurable d) (hgap : ∀ᵐ x ∂μ, g ≤ |d x|) :
    ‖(∫ x, (d x + ξ)⁻¹ • B x ∂μ) - (∫ x, (d x)⁻¹ • B x ∂μ)‖ ≤
      (2 * ξ / g ^ 2) * ∫ x, ‖B x‖ ∂μ := by
  have hgapx : ∀ᵐ x ∂μ, g / 2 ≤ |d x + ξ| := by
    filter_upwards [hgap] with x hx
    have ht := abs_add_le (d x + ξ) (-ξ)
    simp only [add_neg_cancel_right, abs_neg, abs_of_nonneg hξ] at ht
    linarith
  have hi0 := separated_band_integrable B d hg hB hdm hgap
  have hix := separated_band_integrable B (fun x => d x + ξ) (half_pos hg)
    hB (hdm.add_const ξ) hgapx
  rw [← integral_sub hix hi0]
  have hdom := hB.norm.const_mul (2 * ξ / g ^ 2)
  have hbound := norm_integral_le_of_norm_le
    (f := fun x => (d x + ξ)⁻¹ • B x - (d x)⁻¹ • B x) hdom (by
    filter_upwards [hgap] with x hx
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (separated_reciprocal_difference_bound hg hξ hsmall hx) (norm_nonneg (B x)))
  simpa only [integral_const_mul] using hbound

end

end Maxwell.Defect
