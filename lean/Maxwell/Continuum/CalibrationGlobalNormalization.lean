import Maxwell.Continuum.CalibrationGlobalNorm
import Maxwell.Continuum.CalibrationFiniteMode

/-! Exact normalization in the fixed real-coordinate matrix representation,
including positivity of the literal normalization used by the actual mode. -/

namespace Maxwell.Continuum.Calibration.GlobalPower

open scoped BigOperators
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true

theorem normalized_coordinates (R P : ℕ) (x : Fin (2*aliasArraySize R) → ℚ) :
    sample R (FourierData.normalizeData P ⟨R,unpack R x⟩).field=
      (sqrtRationalCenter (∑ i,x i^2) P)⁻¹ • x := by
  rw [FourierData.normalizeData,FourierData.scale_field,normCenter_unpack]
  change (sampleLinear R) (_ • embed R x)=_
  rw [map_smul]
  change _ • sample R (embed R x)=_
  rw [sample_embed]

theorem normalized_data (R P : ℕ) (x : Fin (2*aliasArraySize R) → ℚ) :
    (⟨R,unpack R ((sqrtRationalCenter (∑ i,x i^2) P)⁻¹ • x)⟩ : FourierData)=
      FourierData.normalizeData P ⟨R,unpack R x⟩ := by
  apply FourierData.eq_of_radius_field
  · rfl
  · change embed R ((sqrtRationalCenter (∑ i,x i^2) P)⁻¹ • x)=_
    rw [FourierData.normalizeData,FourierData.scale_field,normCenter_unpack]
    exact (embedLinear R).map_smul _ _

theorem mode_normalized_coordinates (L r N : ℕ) (z : ℚ) :
    sample (modeRadius L r N) (FiniteAlgorithm.mode L r N z).field=
      (FourierData.normCenter (FiniteAlgorithm.precision L r N) (FiniteAlgorithm.rawMode L r N z))⁻¹ •
        PowerMachine.rationalPower (modeMatrix L r N z)
          (sample (modeRadius L r N) (FiniteAlgorithm.seed L r N).field) (FiniteAlgorithm.iterations N) := by
  rw [←normalizedMode_eq,rawMode_normCenter]
  exact normalized_coordinates _ _ _

attribute [local irreducible] FiniteAlgorithm.rawMode FiniteAlgorithm.precision
  FiniteAlgorithm.iterations EffectiveMass.realMode

theorem rawMode_normCenter_pos {L : ℕ} (hL : MasterConstants.Ls≤(L:ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L:ℝ)⁻¹ z) :
    0<FourierData.normCenter (FiniteAlgorithm.precision L r N) (FiniteAlgorithm.rawMode L r N z) := by
  have hn := FiniteAlgorithm.rawMode_norm_lower hL r N z D
  have hp := FiniteAlgorithm.mode_normalize_small L r N
  apply (FourierData.normalizeData_error _ _ _).1
  have hpos : (0:ℝ)≤(1/2:ℝ)^(49+38*FiniteAlgorithm.iterations N) := by positivity
  linarith

#print axioms normalized_data
#print axioms rawMode_normCenter_pos

end Maxwell.Continuum.Calibration.GlobalPower
