import Maxwell.Continuum.FourierTensorModePayload
import Maxwell.Continuum.FourierTensorOutputParameters

/-! The three computed component streams, with the actual compact-template
headers and radial-profile bytes, equal the declared finite output. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost RationalDataflow PartArray Calibration Calibration.Supercell Calibration.FiniteAlgorithm
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] FiniteAlgorithm.mode FiniteAlgorithm.size MasterConstants.exponent

def outputComponentPayload (L r N : ℕ) (z : ℚ)
    (a : Table (2*aliasArraySize (FiniteAlgorithm.mode L r (N+2) z).radius)) (j : Fin 3) : List Bool :=
  componentPayload (FiniteAlgorithm.size L r (N+2))
    (compactNormalizationBits N (lengthBits (FiniteAlgorithm.size L r (N+2)))) L
    (FiniteAlgorithm.mode L r (N+2) z).radius
    (compactFourierBits N (lengthBits (FiniteAlgorithm.size L r (N+2))) (outputSupportBits L r N z))
    (outputFrequency L r N z) (outputTensorPrecision L r N z) a j

def outputTemplateHeader (L r N : ℕ) (z : ℚ) : List Bool :=
  Codec.nat (outputTemplateDegree L r N z)++profileBits (outputTensorPrecision L r N z)++
    Codec.nat (compactFourierBits N (lengthBits (FiniteAlgorithm.size L r (N+2))) (outputSupportBits L r N z)+
      3*waveWorkBits (8*outputFrequency L r N z) (outputTensorPrecision L r N z))++
    Codec.nat (3*(outputTemplateDegree L r N z)^3)

theorem outputTemplateBits_components (L r N : ℕ) (z : ℚ)
    (a : Table (2*aliasArraySize (FiniteAlgorithm.mode L r (N+2) z).radius))
    (ha : GlobalPower.tableData (FiniteAlgorithm.mode L r (N+2) z).radius a=
      FiniteAlgorithm.mode L r (N+2) z) :
    outputTemplateBits L r N z=outputTemplateHeader L r N z++
      outputComponentPayload L r N z a 0++outputComponentPayload L r N z a 1++
      outputComponentPayload L r N z a 2 := by
  have h := vectorBits_components (FiniteAlgorithm.size L r (N+2))
    (compactNormalizationBits N (lengthBits (FiniteAlgorithm.size L r (N+2)))) L
    (FiniteAlgorithm.mode L r (N+2) z).radius
    (compactFourierBits N (lengthBits (FiniteAlgorithm.size L r (N+2))) (outputSupportBits L r N z))
    (outputFrequency L r N z) (outputTensorPrecision L r N z) a
  rw [ha] at h
  have h3 (n : ℕ) : n+n+n=3*n := by omega
  simpa only [outputTemplateBits,compactOutputBits,realCompactBits,compactCoefficient,
    outputTemplateHeader,outputComponentPayload,outputTemplateDegree,outputFrequency,
    outputTensorPrecision,h3,List.append_assoc] using
    congrArg (fun bits => Codec.nat (outputTemplateDegree L r N z)++
      profileBits (outputTensorPrecision L r N z)++bits) h

#print axioms outputTemplateBits_components
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
