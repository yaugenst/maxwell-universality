import Maxwell.Defect.Expansion

/-! The local selected band, shared by the spectral-band and direct
regular-resolvent integral representations. -/

open MeasureTheory Set Real
namespace Maxwell.Defect

structure LocalBandChart (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  radius : ℝ
  coercivity : ℝ
  numeratorRemainder : ℝ
  dispersionRemainder : ℝ
  radius_pos : 0 < radius
  coercivity_pos : 0 < coercivity
  numeratorRemainder_nonneg : 0 ≤ numeratorRemainder
  dispersionRemainder_nonneg : 0 ≤ dispersionRemainder
  numerator : Momentum → F
  dispersion : Momentum → ℝ
  edgeNumerator : F
  quadraticRoot : Momentum ≃L[ℝ] Momentum
  numerator_measurable : AEStronglyMeasurable numerator (volume.restrict (Metric.ball 0 radius))
  dispersion_measurable : Measurable dispersion
  dispersion_coercive : ∀ q ∈ Metric.ball 0 radius, q ≠ 0 →
    coercivity * ‖q‖ ^ 2 ≤ dispersion q
  quadratic_coercive : ∀ q, coercivity * ‖q‖ ^ 2 ≤ ‖quadraticRoot q‖ ^ 2
  dispersion_quartic : ∀ q ∈ Metric.ball 0 radius,
    |dispersion q - ‖quadraticRoot q‖ ^ 2| ≤ dispersionRemainder * ‖q‖ ^ 4
  numerator_quadratic : ∀ q ∈ Metric.ball 0 radius,
    ‖numerator q - edgeNumerator‖ ≤ numeratorRemainder * ‖q‖ ^ 2

namespace LocalBandChart
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def localPart (C : LocalBandChart F) (ξ : ℝ) : F :=
  ∫ q in Metric.ball 0 C.radius, (C.dispersion q + ξ)⁻¹ • C.numerator q

noncomputable def edgeCoefficient (C : LocalBandChart F) : ℝ :=
  1 / (4 * Real.pi * |LinearMap.det C.quadraticRoot.toLinearEquiv.toLinearMap|)

noncomputable def localRemainder (C : LocalBandChart F) : ℝ :=
  4 * Real.pi * C.radius * (C.numeratorRemainder / C.coercivity ^ 2 +
    2 * C.dispersionRemainder * ‖C.edgeNumerator‖ / C.coercivity ^ 3) +
    4 * Real.pi / C.radius * (‖C.edgeNumerator‖ / C.coercivity ^ 2)

theorem edgeCoefficient_pos (C : LocalBandChart F) : 0 < C.edgeCoefficient := by
  have hd := C.quadraticRoot.toLinearEquiv.isUnit_det'.ne_zero
  unfold edgeCoefficient
  positivity

theorem localRemainder_nonneg (C : LocalBandChart F) : 0 ≤ C.localRemainder := by
  have hR := C.radius_pos
  have hc := C.coercivity_pos
  have hN := C.numeratorRemainder_nonneg
  have hD := C.dispersionRemainder_nonneg
  unfold localRemainder
  positivity

theorem localPart_integrable (C : LocalBandChart F) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    IntegrableOn (fun q => (C.dispersion q + ξ)⁻¹ • C.numerator q)
      (Metric.ball 0 C.radius) :=
  local_band_integrable C.numerator C.dispersion C.edgeNumerator C.coercivity_pos
    hξ C.numerator_measurable C.dispersion_measurable C.dispersion_coercive
    C.numerator_quadratic

theorem dispersion_upper (C : LocalBandChart F) (q : Momentum)
    (hq : q ∈ Metric.ball 0 C.radius) :
    C.dispersion q ≤
      (‖C.quadraticRoot.toContinuousLinearMap‖ ^ 2 +
        C.dispersionRemainder * C.radius ^ 2 + 1) * ‖q‖ ^ 2 := by
  have hnorm : ‖q‖ < C.radius := by simpa using hq
  have hL := pow_le_pow_left₀ (norm_nonneg (C.quadraticRoot q))
    (C.quadraticRoot.toContinuousLinearMap.le_opNorm q) 2
  rw [mul_pow] at hL
  have hR : ‖q‖ ^ 2 ≤ C.radius ^ 2 := by
    nlinarith [norm_nonneg q, C.radius_pos]
  have herr := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hR (sq_nonneg ‖q‖)) C.dispersionRemainder_nonneg
  have hh := (abs_le.mp (C.dispersion_quartic q hq)).2
  nlinarith [sq_nonneg ‖q‖]

/-- Combine the actual local pole integral with any separately proved
regular contribution. Its bound comes from the regular resolvent identity. -/
theorem sqrt_expansion [CompleteSpace F] (C : LocalBandChart F)
    (regular : ℝ → F) {ξ K : ℝ} (hξ : 0 < ξ)
    (hreg : ‖regular 0 - regular ξ‖ ≤ K * ξ) :
    ‖(1 / (2 * Real.pi) ^ 3 : ℝ) • (C.localPart 0 + regular 0) -
      (1 / (2 * Real.pi) ^ 3 : ℝ) • (C.localPart ξ + regular ξ) -
      (C.edgeCoefficient * Real.sqrt ξ) • C.edgeNumerator‖ ≤
      ((C.localRemainder + K) / (2 * Real.pi) ^ 3) * ξ := by
  let κ : ℝ := 2 * Real.pi ^ 2 * Real.sqrt ξ /
    |LinearMap.det C.quadraticRoot.toLinearEquiv.toLinearMap|
  have hlocal : ‖C.localPart 0 - C.localPart ξ - κ • C.edgeNumerator‖ ≤
      C.localRemainder * ξ := by
    simpa only [localPart, localRemainder, add_zero] using
      local_compressed_sqrt_expansion C.numerator C.dispersion C.edgeNumerator
        C.quadraticRoot C.radius_pos C.coercivity_pos C.numeratorRemainder_nonneg hξ
        C.numerator_measurable C.dispersion_measurable C.dispersion_coercive
        C.quadratic_coercive C.dispersion_quartic C.numerator_quadratic
  have hk : (1 / (2 * Real.pi) ^ 3 : ℝ) * κ = C.edgeCoefficient * Real.sqrt ξ := by
    dsimp [κ, edgeCoefficient]
    field_simp
    ring
  rw [← hk, mul_smul]
  have hid :
      (1 / (2 * Real.pi) ^ 3 : ℝ) • (C.localPart 0 + regular 0) -
        (1 / (2 * Real.pi) ^ 3 : ℝ) • (C.localPart ξ + regular ξ) -
        (1 / (2 * Real.pi) ^ 3 : ℝ) • κ • C.edgeNumerator =
      (1 / (2 * Real.pi) ^ 3 : ℝ) •
        ((C.localPart 0 - C.localPart ξ - κ • C.edgeNumerator) +
          (regular 0 - regular ξ)) := by
    simp only [smul_add, smul_sub]
    abel
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hh := mul_le_mul_of_nonneg_left
    ((norm_add_le _ _).trans (add_le_add hlocal hreg))
    (show (0 : ℝ) ≤ 1 / (2 * Real.pi) ^ 3 by positivity)
  convert hh using 1; ring

end LocalBandChart
end Maxwell.Defect
