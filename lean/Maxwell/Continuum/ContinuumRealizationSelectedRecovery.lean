import Maxwell.Continuum.ContinuumRealizationResources
import Maxwell.Continuum.ContinuumRealizationRecovery

/-! The concrete continuum output at the selected binary precisions.
Only certified finite enclosures, a finite template approximation, the
solver residual, and the reported volume moments enter the recovery
interface. All analytic and scalar precision budgets are discharged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Maxwell.Continuum.RealizationParameters

open MasterConstants Maxwell.Composition Auxiliary EffectiveMass FiniteAuxiliary MeasureTheory
attribute [local irreducible] Cs exponent Ls Parameters.sourceInput muH realMode pecCurlCurl

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
local instance selectedFiniteRecoveryDecidableEq : DecidableEq (SourceIncidence.V S (precision p S hm)) :=
  realEncodedRecoveryDecidableEq S (precision p S hm)

def enclosuresOfPrecision (I : Calibration.RationalInterval)
    (J : Fin 3 → Calibration.RationalInterval)
    (hI : I.Contains (muH (energyCalibration p S hm)
      (inverse_length_le_1024 (length_master p S hm))))
    (hIw : I.width ≤ (1/2 : ℚ)^(calibrationPrecision p S hm))
    (hJ : ∀ j, (J j).Contains (usefulCoupling (length_master p S hm)
      (energyCalibration p S hm) (spacing p S hm) j))
    (hJw : ∀ j, (J j).width ≤ (1/2 : ℚ)^(calibrationPrecision p S hm)) : Enclosures p S hm where
  mode := I
  coupling := J
  mode_contains := hI
  mode_width := (hIw.trans (calibration_coupling_budget p S hm)).trans (by
    have hz : (0 : ℚ) ≤ (zeta p S hm)^2 := sq_nonneg _
    linarith only [hz])
  coupling_contains := hJ
  coupling_width := fun j => (hJw j).trans (calibration_coupling_budget p S hm)

theorem template_norm_of_precision (a : FieldL2)
    (r : Space)
    (ha : ‖a-siteInsertion (length p S hm : ℝ)⁻¹ r
      (realMode (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm)))‖ ≤
        (1/2 : ℝ)^(templatePrecision p S)) : ‖a‖ ≤ 2 := by
  have hu := (siteInsertion (length p S hm : ℝ)⁻¹ r).le_opNorm
    (realMode (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm)))
  rw [realMode_norm, mul_one] at hu
  have hu1 := hu.trans (siteInsertion_norm _ _)
  have ht := norm_le_norm_sub_add a (siteInsertion (length p S hm : ℝ)⁻¹ r
    (realMode (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm))))
  have he : (1/2 : ℝ)^(templatePrecision p S) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith only [ht, hu1, ha, he]

theorem selected_every_field_recovery (hm2 : 2 ≤ S.nnz) (hp : Source.Promises p S)
    (hb : S.source ≠ 0) (C : Enclosures p S hm)
    (hC : C.mode.width ≤ (1/2 : ℚ)^(calibrationPrecision p S hm))
    (a : SourceDecoration.Vertex S (precision p S hm) → FieldL2)
    (hsa : ∀ i k, ∀ᵐ x ∂volume,
      x ∉ Metric.ball (centers p S hm i) (length p S hm : ℝ) → a i k x = 0)
    (ha : ∀ i, ‖a i-siteInsertion (length p S hm : ℝ)⁻¹ (centers p S hm i)
      (realMode (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm)))‖ ≤
        (1/2 : ℝ)^(templatePrecision p S))
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
    fieldConjugation (outputSource p S hm (sourcePrecision p S) C.sourceScalar a hsa : FieldL2) =
      (outputSource p S hm (sourcePrecision p S) C.sourceScalar a hsa : FieldL2) ∧
    (∀ i, fieldConjugation (fieldRealProjection (a i)) = fieldRealProjection (a i)) ∧
    Source.ResidualTarget S ((accuracy p S hm : ℝ)/4)
      (sparseMomentDecode S (precision p S hm)
        (weightedMomentValues (momentPrecision p S) C.wellStrength w)) := by
  have hCR : (C.mode.width : ℝ) ≤ (1/2 : ℝ)^(calibrationPrecision p S hm) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hC
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  exact every_field_recovery p S hm hm2 hp hb C (materialPrecision p S)
    (sourceTolerance_pos p S).le (sourceTolerance_bound p S hm hm2 hp.1)
    (material_precision_budget p S hm hm2 hp.1) a
    (fun i => template_norm_of_precision p S hm (a i) (centers p S hm i) (ha i)) hsa
    (fun i => (ha i).trans (template_precision_budget p S hm hm2 hp.1))
    (sourcePrecision p S) C.sourceScalar
    (C.sourceScalar_tolerance (hCR.trans (calibration_source_budget p S hm)))
    (source_precision_budget p S) j hgood u hu (momentPrecision p S) w
    (moment_precision_budget p S hm hm2 hp.1) hw

#print axioms enclosuresOfPrecision
#print axioms template_norm_of_precision
#print axioms selected_every_field_recovery

end Maxwell.Continuum.RealizationParameters
