import Maxwell.Continuum.ContinuumRealizationMaterial
import Maxwell.Continuum.FiniteAuxiliaryRealEncodedRecovery
import Maxwell.Continuum.FiniteAuxiliarySourceEncodingSupport

/-! Every-field recovery specialized to the actual continuum parameter
search, rational energy/tuning, encoded material, and sampled PEC inverse.
Only the concrete finite template and output-precision checks remain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Maxwell.Continuum.RealizationParameters

open MasterConstants Maxwell.Composition Auxiliary EffectiveMass FiniteAuxiliary MeasureTheory
attribute [local irreducible] Cs exponent Ls Parameters.sourceInput muH realMode pecCurlCurl

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
local instance selectedRecoveryDecidableEq : DecidableEq (SourceIncidence.V S (precision p S hm)) :=
  realEncodedRecoveryDecidableEq S (precision p S hm)

def outputSource (P : ℕ) (ĉ : ℚ)
    (a : SourceDecoration.Vertex S (precision p S hm) → FieldL2)
    (hsa : ∀ i k, ∀ᵐ x ∂volume,
      x ∉ Metric.ball (centers p S hm i) (length p S hm : ℝ) → a i k x = 0) :
    testL2Closure (BoxModes.boxDomain (BoxCutoff.side (box p S hm))) :=
  ⟨emittedSource S (precision p S hm) P ĉ (fun i => fieldRealProjection (a i)),
    emittedSource_mem_PEC S (precision p S hm) P ĉ (box p S hm)
      (by positivity : (0 : ℝ) ≤ buffer p S hm) (centers p S hm) (centers_buffered p S hm)
      (fun i => fieldRealProjection (a i))
      (fun i => fieldRealProjection_supported (a i)
        (Metric.ball (centers p S hm i) (length p S hm : ℝ)) (hsa i))⟩

theorem outputSource_real (P : ℕ) (ĉ : ℚ)
    (a : SourceDecoration.Vertex S (precision p S hm) → FieldL2)
    (hsa : ∀ i k, ∀ᵐ x ∂volume,
      x ∉ Metric.ball (centers p S hm i) (length p S hm : ℝ) → a i k x = 0) :
    fieldConjugation (outputSource p S hm P ĉ a hsa : FieldL2) =
      (outputSource p S hm P ĉ a hsa : FieldL2) :=
  projected_emittedSource_real S (precision p S hm) P ĉ a

theorem every_field_recovery (hm2 : 2 ≤ S.nnz) (hp : Source.Promises p S) (hb : S.source ≠ 0)
    (C : Enclosures p S hm) (N : ℕ) {ef : ℝ} (hef0 : 0 ≤ ef)
    (hef : ef ≤ (residual p S hm : ℝ)/4)
    (hN : Enclosures.materialError p S hm N*
      ((2 : ℝ)^142*(budget p S hm : ℝ)*(length p S hm : ℝ)^2) ≤ (residual p S hm : ℝ)/4)
    (a : SourceDecoration.Vertex S (precision p S hm) → FieldL2)
    (ha : ∀ i, ‖a i‖ ≤ 2)
    (hsa : ∀ i k, ∀ᵐ x ∂volume,
      x ∉ Metric.ball (centers p S hm i) (length p S hm : ℝ) → a i k x = 0)
    (haerror : ∀ i, ‖a i-siteInsertion (length p S hm : ℝ)⁻¹ (centers p S hm i)
      (realMode (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm)))‖ ≤
        min (ef/4) ((residual p S hm : ℝ)/4))
    (P : ℕ) (ĉ : ℚ)
    (hĉ : |(ĉ : ℝ)-(alpha p S hm : ℝ)/
      muH (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm))| ≤ ef/16)
    (hP : (S.nnz : ℝ)*(1/2 : ℝ)^P ≤ ef/16)
    (j : Fin (drawCount p S hm)) (hgood : j.val ∉ C.badDraws hb N)
    (u : OperatorDomain (BoxModes.boxDomain (BoxCutoff.side (box p S hm))))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
      (C.outputDielectric hb N j) u-outputSource p S hm P ĉ a hsa‖ ≤
        (residual p S hm : ℝ)*‖outputSource p S hm P ĉ a hsa‖)
    (Pm : ℕ) (w : SourceDecoration.Vertex S (precision p S hm) → ℚ)
    (hPm : (1/2 : ℝ)^Pm ≤
      (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ)))
    (hw : ∀ i, |(w i : ℝ)-(inner ℂ (fieldRealProjection (a i))
      (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))) u)).re| ≤
        (epsilon p S hm : ℝ)/(2^27*max 1 (sites p S hm : ℝ))) :
    fieldConjugation (outputSource p S hm P ĉ a hsa : FieldL2) =
      (outputSource p S hm P ĉ a hsa : FieldL2) ∧
    (∀ i, fieldConjugation (fieldRealProjection (a i)) = fieldRealProjection (a i)) ∧
    Source.ResidualTarget S ((accuracy p S hm : ℝ)/4)
      (sparseMomentDecode S (precision p S hm) (weightedMomentValues Pm C.wellStrength w)) := by
  obtain ⟨R, hR, _hg, _hc⟩ := C.good_draw_inverse hb N j hgood
  have hs := sample_bounds p S hm j
  have hdiag (i : SourceDecoration.Vertex S (precision p S hm)) :=
    targetDiagonal_bound p S hm (energyCalibration p S hm) hb C.coupling
      C.coupling_contains C.coupling_width i
  have hv (i : SourceDecoration.Vertex S (precision p S hm)) := (C.wellStrength_spec hb i).2.2
  have heps : (epsilon p S hm : ℝ) =
      (PhysicalAccuracy.epsilon S (precision p S hm) (accuracy p S hm) : ℝ)/16 := by
    rw [epsilon_eq, Rat.cast_div, Rat.cast_ofNat]
  refine real_encoded_every_field_recovery S (precision p S hm) hp.1 hm2 hb
    (precision_pos p S hm) (rounding_small p S hm hm2 hp)
    (kappa_ge_one p S hm) (alpha_pos p S hm) (spacing_bounds p S hm).2.2.1
    (budget_ge_one p S hm) (source_condition p S hm hm2 hp) (budget_eq p S hm).ge
    (length_master p S hm) (energyCalibration p S hm) hs.1 hs.2.1 (spacing_pos p S hm)
    C.wellStrength (fun i => by exact_mod_cast (C.wellStrength_spec hb i).1)
    (fun i => (C.wellStrength_spec hb i).2.1) (fun k => (couplingValue p S hm C.coupling k : ℝ))
    (epsilon_pos p S hm).le (epsilon_le_one p S hm)
    (by simpa only [← zeta_cast p S hm] using (spacing_bounds p S hm).2.2.2.1)
    (by simpa only [← zeta_cast p S hm] using (spacing_bounds p S hm).2.2.2.2)
    ?_ ?_ ?_ ?_ ?_ ?_ (shift p S hm) (box p S hm)
    (by positivity : (0 : ℝ) ≤ buffer p S hm) (centers_buffered p S hm)
    (residual_pos p S hm).le (residual_half p S hm) (residual_identity p S hm)
    hef0 hef (residual_exponentials p S hm) hN a ha hsa haerror P ĉ hĉ hP
    (C.outputDielectric hb N j) (C.outputDielectric_multiplier_error hb N j)
    R hR u (outputSource p S hm P ĉ a hsa) rfl hu Pm w hPm hw
    (accuracy p S hm) (accuracy_pos p S hm) (accuracy_le_one p S hm)
    (precision_budget p S hm) heps
  · intro i
    simpa only [targetDiagonal, PhysicalDiagonal.diagonal_cast] using hdiag i
  · intro i
    simpa only [targetDiagonal, PhysicalDiagonal.diagonal_cast, zeta_cast] using hv i
  · intro k
    simpa only [zeta_cast] using coupling_error p S hm (energyCalibration p S hm)
      C.coupling C.coupling_contains C.coupling_width k
  · exact coupling_lower p S hm (energyCalibration p S hm) hb C.coupling
      C.coupling_contains C.coupling_width
  · simpa only [zeta_cast] using interaction_tail p S hm
  · simpa only [zeta_cast] using hs.2.2

#print axioms outputSource_real
#print axioms every_field_recovery

end Maxwell.Continuum.RealizationParameters
