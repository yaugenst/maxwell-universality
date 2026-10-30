import Maxwell.Continuum.CalibrationCompactModeBits

/-! Individual words and tensor degrees of the literal compact output.
These bounds refer to the actual emitted dyadic coefficients. -/

namespace Maxwell.Continuum.Calibration.FiniteAlgorithm
open Supercell Profile
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
attribute [local irreducible] MasterConstants.exponent size precision mode rootDegree
  outputArithmeticCoefficient

def outputFrequency (L r N : ℕ) (z : ℚ) : ℕ :=
  templateFrequencyBound (size L r (N+2)) (L : ℚ) (mode L r (N+2) z).radius

def outputTensorPrecision (L r N : ℕ) (z : ℚ) : ℕ :=
  compactTensorBits N (lengthBits L) (outputSupportBits L r N z)

def outputTemplateDegree (L r N : ℕ) (z : ℚ) : ℕ :=
  waveDegree (8*outputFrequency L r N z) (outputTensorPrecision L r N z)

def outputTemplateCoefficient (L r N : ℕ) (z : ℚ) (c : Fin 3)
    (j : Fin 3→Fin (outputTemplateDegree L r N z)) :=
  realFourierTensorCoefficient
    (PeriodicSampling.Product.frequencyCube (mode L r (N+2) z).radius)
    (templateFrequency (size L r (N+2)) (L : ℚ))
    (fun n => compactCoefficient (size L r (N+2)) N (lengthBits (size L r (N+2)))
      (outputSupportBits L r N z) (mode L r (N+2) z) n c)
    (outputFrequency L r N z) (outputTensorPrecision L r N z) j

def outputWordCoefficient (C : ℕ) : ℕ :=
  2*outputArithmeticCoefficient C+3*wavePrecisionCoefficient (outputArithmeticCoefficient C)+16

theorem outputTemplateDegree_polynomial {L r N C ℓ : ℕ} (hL0 : 0<L) (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) (z : ℚ) :
    outputTemplateDegree L r N z≤waveDegreeCoefficient (outputArithmeticCoefficient C)*ℓ^8 :=
  waveDegree_polylog hℓ (output_frequency_polynomial hL0 hℓ hL hr hN z)
    (output_precisions_linear hL0 hℓ hL hr hN z).1

theorem outputTemplateCoefficient_bits {L r N C ℓ : ℕ} (hL0 : 0<L) (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) (z : ℚ)
    (hv : ‖(mode L r (N+2) z).value‖≤2) (c : Fin 3)
    (j : Fin 3→Fin (outputTemplateDegree L r N z)) :
    (outputTemplateCoefficient L r N z c j).numeratorBits≤outputWordCoefficient C*ℓ := by
  have hp := output_precisions_linear hL0 hℓ hL hr hN z
  have hw := waveWorkBits_polylog hℓ (output_frequency_polynomial hL0 hℓ hL hr hN z) hp.1
  have hb := realFinalVectorCoefficient_bits
    (PeriodicSampling.Product.frequencyCube (mode L r (N+2) z).radius)
    (templateFrequency (size L r (N+2)) (L : ℚ))
    (fun i n => compactCoefficient (size L r (N+2)) N (lengthBits (size L r (N+2)))
      (outputSupportBits L r N z) (mode L r (N+2) z) n i)
    (outputFrequency L r N z) (outputTensorPrecision L r N z)
    (compactMassBits (outputSupportBits L r N z))
    (fun n hn i => templateFrequency_computed_bound _ _ _ hn i)
    (compactCoefficient_component_mass _ _ _ _ _ hv (lengthBits_bound _)) c j
  change (outputTemplateCoefficient L r N z c j).numeratorBits≤_ at hb
  unfold outputWordCoefficient
  dsimp only [outputFrequency,outputTensorPrecision] at hb
  apply hb.trans
  nlinarith only [hp.2.1,hp.2.2,hw,hℓ]

theorem outputTemplateDenominator_linear {L r N C ℓ : ℕ} (hL0 : 0<L) (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) (z : ℚ) :
    compactFourierBits N (lengthBits (size L r (N+2))) (outputSupportBits L r N z)+
      3*waveWorkBits (8*outputFrequency L r N z) (outputTensorPrecision L r N z)≤
        outputWordCoefficient C*ℓ := by
  have hp := output_precisions_linear hL0 hℓ hL hr hN z
  have hw := waveWorkBits_polylog hℓ (output_frequency_polynomial hL0 hℓ hL hr hN z) hp.1
  unfold outputWordCoefficient
  dsimp only [outputFrequency,outputTensorPrecision]
  nlinarith only [hp.2.1,hw,hℓ]

#print axioms outputTemplateDegree_polynomial
#print axioms outputTemplateCoefficient_bits
#print axioms outputTemplateDenominator_linear
end Maxwell.Continuum.Calibration.FiniteAlgorithm
