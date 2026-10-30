import Maxwell.Continuum.ContinuumRealizationSelectedRecovery

/-! The selected source and genuine PEC inverse bound every allowed raw
moment report. Consequently the fixed signed words cover every solver
field satisfying the required residual, with no extra range promise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Maxwell.Continuum.RealizationParameters

open MasterConstants Maxwell.Composition Auxiliary EffectiveMass FiniteAuxiliary MeasureTheory
attribute [local irreducible] Cs exponent Ls Parameters.sourceInput muH realMode pecCurlCurl

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
local instance selectedReportDecidableEq : DecidableEq (SourceIncidence.V S (precision p S hm)) :=
  realEncodedRecoveryDecidableEq S (precision p S hm)

variable (hm2 : 2 ≤ S.nnz) (huS : IsUnit (Source.realMatrix S)) (hb : S.source ≠ 0)
  (C : Enclosures p S hm)
  (hC : C.mode.width ≤ (1/2 : ℚ)^(calibrationPrecision p S hm))
  (a : SourceDecoration.Vertex S (precision p S hm) → FieldL2)
  (hsa : ∀ i k, ∀ᵐ x ∂volume,
    x ∉ Metric.ball (centers p S hm i) (length p S hm : ℝ) → a i k x = 0)
  (ha : ∀ i, ‖a i-siteInsertion (length p S hm : ℝ)⁻¹ (centers p S hm i)
    (realMode (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm)))‖ ≤
      (1/2 : ℝ)^(templatePrecision p S))

include hm2 huS hb hC ha in
theorem selected_source_error :
    ‖(outputSource p S hm (sourcePrecision p S) C.sourceScalar a hsa : FieldL2)-
      idealSource (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm))
        (centers p S hm) (alpha p S hm) (routedForcing S (precision p S hm))‖ ≤
      (sourceTolerance p S : ℝ)*‖routedForcing S (precision p S hm)‖ := by
  have hCR : (C.mode.width : ℝ) ≤ (1/2 : ℝ)^(calibrationPrecision p S hm) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hC
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  exact emittedSource_error S (precision p S hm) huS hb (length_master p S hm)
    (energyCalibration p S hm) (alpha_pos p S hm).le (spacing_bounds p S hm).2.2.1
    (centers p S hm) (centers_disjoint p S hm) (fun i => fieldRealProjection (a i))
    (fun i => (fieldRealProjection_norm (a i)).trans
      (template_norm_of_precision p S hm (a i) (centers p S hm i) (ha i)))
    (fun i => fieldRealProjection_supported (a i) _ (hsa i))
    (sourceTolerance_pos p S).le
    (fun i => (real_template_error (energyCalibration p S hm)
      (inverse_length_le_1024 (length_master p S hm)) (centers p S hm i) (a i)).trans
      ((ha i).trans ((template_precision_budget p S hm hm2 huS).trans (min_le_left _ _))))
    (sourcePrecision p S) C.sourceScalar
    (C.sourceScalar_tolerance (hCR.trans (calibration_source_budget p S hm)))
    (source_precision_budget p S)

include hm2 huS hb hC ha in
theorem selected_source_norm :
    ‖outputSource p S hm (sourcePrecision p S) C.sourceScalar a hsa‖ ≤
      2*‖routedForcing S (precision p S hm)‖ := by
  have hf := selected_source_error p S hm hm2 huS hb C hC a hsa ha
  have hn := finite_source_norm_le (length_master p S hm) (energyCalibration p S hm)
    (centers p S hm) (alpha_pos p S hm).le (spacing_bounds p S hm).2.2.1
    (centers_disjoint p S hm) (routedForcing S (precision p S hm))
    (outputSource p S hm (sourcePrecision p S) C.sourceScalar a hsa : FieldL2) hf
  have hef : (sourceTolerance p S : ℝ) ≤ 1 := by
    exact (sourceTolerance_bound p S hm hm2 huS).trans
      (by linarith only [residual_half p S hm])
  have hg := norm_nonneg (routedForcing S (precision p S hm))
  have hh := mul_le_mul_of_nonneg_right hef hg
  change ‖(outputSource p S hm (sourcePrecision p S) C.sourceScalar a hsa : FieldL2)‖ ≤ _
  linarith only [hn, hh]

include hm2 huS hb hC ha in
theorem selected_report_range
    (j : Fin (drawCount p S hm)) (hgood : j.val ∉ C.badDraws hb (materialPrecision p S))
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (C.outputDielectric hb (materialPrecision p S) j) u-
        outputSource p S hm (sourcePrecision p S) C.sourceScalar a hsa‖ ≤
      (residual p S hm : ℝ)*‖outputSource p S hm (sourcePrecision p S) C.sourceScalar a hsa‖)
    (w : SourceDecoration.Vertex S (precision p S hm) → ℚ)
    (hw : ∀ i, |(w i : ℝ)-(inner ℂ (fieldRealProjection (a i))
      (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))) u)).re| ≤
        (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ))) :
    ∀ i, |w i| < 8*inverseBound p S hm*S.nnz := by
  obtain ⟨R, hR, _hg, _hc⟩ := C.good_draw_inverse hb (materialPrecision p S) j hgood
  have hE := approximate_field_norm _ _ R hR (residual_half p S hm) u
    (outputSource p S hm (sourcePrecision p S) C.sourceScalar a hsa)
    (selected_source_norm p S hm hm2 huS hb C hC a hsa ha) hu
  have hδ : (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ)) ≤ 1 := by
    have hmax : (1 : ℝ) ≤ max 1 (sites p S hm : ℝ) := le_max_left _ _
    apply (div_le_iff₀ (by positivity)).mpr
    have hpow : (1 : ℝ) ≤ 2^27 := by norm_num
    have hh := mul_le_mul hpow hmax zero_le_one (by positivity : (0 : ℝ) ≤ 2^27)
    simp only [one_mul] at hh ⊢
    exact (epsilon_le_one p S hm).trans hh
  intro i
  have hm1 : (1 : ℝ) ≤ S.nnz := by exact_mod_cast hm
  have hx := routed_raw_moment_bound S (precision p S hm) huS hb hm _ _
    (inverseBound_pos p S hm).le hE
    ((fieldRealProjection_norm (a i)).trans
      (template_norm_of_precision p S hm (a i) (centers p S hm i) (ha i)))
  have hh := rational_report_range (inverseBound_ge_one p S hm) hm1 hx hδ (w i) (hw i)
  exact_mod_cast hh

#print axioms selected_source_error
#print axioms selected_source_norm
#print axioms selected_report_range

end Maxwell.Continuum.RealizationParameters
