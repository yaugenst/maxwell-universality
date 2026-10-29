import Maxwell.Defect.LocalBandChart

/-! A local band plus separated-band integral representation, with the
normalized compressed-resolvent expansion proved from its chart estimates. -/

open MeasureTheory Set Real

namespace Maxwell.Defect

structure IntegralChart (F X : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace X] (μ : Measure X) extends LocalBandChart F where
  gap : ℝ
  gap_pos : 0 < gap
  farNumerator : X → F
  farDispersion : X → ℝ
  farNumerator_integrable : Integrable farNumerator μ
  farDispersion_measurable : Measurable farDispersion
  far_gap : ∀ᵐ x ∂μ, gap ≤ |farDispersion x|

namespace IntegralChart

variable {F X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace X] {μ : Measure X}

noncomputable def localPart (C : IntegralChart F X μ) (ξ : ℝ) : F :=
  ∫ q in Metric.ball 0 C.radius, (C.dispersion q + ξ)⁻¹ • C.numerator q

noncomputable def farPart (C : IntegralChart F X μ) (ξ : ℝ) : F :=
  ∫ x, (C.farDispersion x + ξ)⁻¹ • C.farNumerator x ∂μ

/-- The Fourier normalization is Lebesgue momentum divided by `(2π)^3`. -/
noncomputable def compression (C : IntegralChart F X μ) (ξ : ℝ) : F :=
  (1 / (2 * Real.pi) ^ 3 : ℝ) • (C.localPart ξ + C.farPart ξ)

noncomputable def edgeCoefficient (C : IntegralChart F X μ) : ℝ :=
  1 / (4 * Real.pi * |LinearMap.det C.quadraticRoot.toLinearEquiv.toLinearMap|)

noncomputable def remainderConstant (C : IntegralChart F X μ) : ℝ :=
  (4 * Real.pi * C.radius * (C.numeratorRemainder / C.coercivity ^ 2 +
      2 * C.dispersionRemainder * ‖C.edgeNumerator‖ / C.coercivity ^ 3) +
    4 * Real.pi / C.radius * (‖C.edgeNumerator‖ / C.coercivity ^ 2) +
    2 / C.gap ^ 2 * ∫ x, ‖C.farNumerator x‖ ∂μ) / (2 * Real.pi) ^ 3

theorem edgeCoefficient_pos (C : IntegralChart F X μ) : 0 < C.edgeCoefficient := by
  have hd := C.quadraticRoot.toLinearEquiv.isUnit_det'.ne_zero
  unfold edgeCoefficient
  positivity

theorem remainderConstant_nonneg (C : IntegralChart F X μ) : 0 ≤ C.remainderConstant := by
  have hR := C.radius_pos
  have hc := C.coercivity_pos
  have hN := C.numeratorRemainder_nonneg
  have hD := C.dispersionRemainder_nonneg
  have hg := C.gap_pos
  have hi : 0 ≤ ∫ x, ‖C.farNumerator x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  unfold remainderConstant
  positivity

theorem sqrt_expansion [CompleteSpace F] (C : IntegralChart F X μ) {ξ : ℝ}
    (hξ : 0 < ξ) (hsmall : ξ ≤ C.gap / 2) :
    ‖C.compression 0 - C.compression ξ -
      (C.edgeCoefficient * Real.sqrt ξ) • C.edgeNumerator‖ ≤ C.remainderConstant * ξ := by
  let κ : ℝ := 2 * Real.pi ^ 2 * Real.sqrt ξ /
    |LinearMap.det C.quadraticRoot.toLinearEquiv.toLinearMap|
  let localC : ℝ := 4 * Real.pi * C.radius *
    (C.numeratorRemainder / C.coercivity ^ 2 +
      2 * C.dispersionRemainder * ‖C.edgeNumerator‖ / C.coercivity ^ 3) +
    4 * Real.pi / C.radius * (‖C.edgeNumerator‖ / C.coercivity ^ 2)
  have hlocal : ‖C.localPart 0 - C.localPart ξ - κ • C.edgeNumerator‖ ≤ localC * ξ := by
    simpa only [localPart, add_zero] using local_compressed_sqrt_expansion
      C.numerator C.dispersion C.edgeNumerator C.quadraticRoot C.radius_pos
      C.coercivity_pos C.numeratorRemainder_nonneg hξ C.numerator_measurable
      C.dispersion_measurable C.dispersion_coercive C.quadratic_coercive
      C.dispersion_quartic C.numerator_quadratic
  have hfar : ‖C.farPart 0 - C.farPart ξ‖ ≤
      (2 * ξ / C.gap ^ 2) * ∫ x, ‖C.farNumerator x‖ ∂μ := by
    rw [norm_sub_rev]
    simpa only [farPart, add_zero] using separated_band_difference_bound
      C.farNumerator C.farDispersion C.gap_pos hξ.le hsmall
      C.farNumerator_integrable C.farDispersion_measurable C.far_gap
  have hk : (1 / (2 * Real.pi) ^ 3 : ℝ) * κ = C.edgeCoefficient * Real.sqrt ξ := by
    dsimp [κ, edgeCoefficient]
    field_simp
    ring
  have hid : C.compression 0 - C.compression ξ -
      (C.edgeCoefficient * Real.sqrt ξ) • C.edgeNumerator =
      (1 / (2 * Real.pi) ^ 3 : ℝ) •
        ((C.localPart 0 - C.localPart ξ - κ • C.edgeNumerator) +
          (C.farPart 0 - C.farPart ξ)) := by
    rw [← hk]
    simp only [compression, smul_add, smul_sub, smul_smul]
    abel
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsum := (norm_add_le _ _).trans (add_le_add hlocal hfar)
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ (1 / (2 * Real.pi) ^ 3 : ℝ))
  convert hscaled using 1; dsimp [remainderConstant, localC]; ring

theorem norm_compression_difference_le [CompleteSpace F] (C : IntegralChart F X μ)
    {ξ : ℝ} (hξ : 0 < ξ) (hsmall : ξ ≤ C.gap / 2) :
    ‖C.compression ξ - C.compression 0‖ ≤
      C.edgeCoefficient * Real.sqrt ξ * ‖C.edgeNumerator‖ + C.remainderConstant * ξ := by
  have h := C.sqrt_expansion hξ hsmall
  have ht := norm_le_norm_add_norm_sub
    ((C.edgeCoefficient * Real.sqrt ξ) • C.edgeNumerator)
    (C.compression 0 - C.compression ξ)
  rw [norm_sub_rev ((C.edgeCoefficient * Real.sqrt ξ) • C.edgeNumerator)
    (C.compression 0 - C.compression ξ)] at ht
  have hcoeff : 0 ≤ C.edgeCoefficient * Real.sqrt ξ :=
    mul_nonneg C.edgeCoefficient_pos.le (Real.sqrt_nonneg ξ)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoeff] at ht
  rw [norm_sub_rev]
  linarith

/-- The finite limiting compression exists in operator norm. This does not
assert existence of an infinite-volume inverse at the spectral edge. -/
theorem compression_tendsto_zero [CompleteSpace F] (C : IntegralChart F X μ) :
    Filter.Tendsto C.compression (nhdsWithin 0 (Ioi 0)) (nhds (C.compression 0)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hcont : Continuous (fun ξ : ℝ =>
      C.edgeCoefficient * Real.sqrt ξ * ‖C.edgeNumerator‖ + C.remainderConstant * ξ) := by
    fun_prop
  have hlim : Filter.Tendsto (fun ξ : ℝ =>
      C.edgeCoefficient * Real.sqrt ξ * ‖C.edgeNumerator‖ + C.remainderConstant * ξ)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  have hsmall : ∀ᶠ ξ in nhdsWithin 0 (Ioi 0), ξ < C.gap / 2 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds (half_pos C.gap_pos))
  filter_upwards [eventually_mem_nhdsWithin, hsmall] with ξ hξ hs
  exact C.norm_compression_difference_le hξ hs.le

end IntegralChart

end Maxwell.Defect
