import Maxwell.Continuum.CalibrationCompactModeResources
import Maxwell.Continuum.CalibrationCompactModeOutput
import Maxwell.Continuum.CalibrationFiniteResources

/-! Polylogarithmic size of the literal compact template emitted from
the actual finite mode program, including its computed logarithms and
all physical-normalization and dyadic-rounding guard bits. -/

namespace Maxwell.Continuum.Calibration.FiniteAlgorithm

open Supercell Profile

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] MasterConstants.exponent size precision mode rootDegree
  sizeCoefficient linearCoefficient supportResourceCoefficient frequencyResourceCoefficient

def radiusCoefficient (C : ℕ) : ℕ := supportResourceCoefficient (linearCoefficient C)*sizeCoefficient C
def radiusLogCoefficient (C : ℕ) : ℕ := Nat.clog 2 (2*radiusCoefficient C+2)+11
def outputFrequencyCoefficient (C : ℕ) : ℕ := frequencyResourceCoefficient (linearCoefficient C)

theorem mode_radius_polynomial {L r N C ℓ : ℕ} (hL0 : 0<L) (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) (z : ℚ) :
    (mode L r N z).radius≤radiusCoefficient C*ℓ^11 := by
  rcases parameters_linear hℓ hL hr hN with ⟨_,_,hn,_,hb,hw,hk,_⟩
  have hs := mode_support_bound hL0 r N (linearCoefficient C) ℓ z hℓ hw hb hk hn
  have hm := size_polynomial hℓ hL hr hN
  calc
    _ ≤ supportResourceCoefficient (linearCoefficient C)*size L r N*ℓ^3 := hs
    _ ≤ supportResourceCoefficient (linearCoefficient C)*(sizeCoefficient C*ℓ^8)*ℓ^3 := by gcongr
    _ = _ := by unfold radiusCoefficient; ring

theorem mode_support_logarithm {L r N C ℓ : ℕ} (hL0 : 0<L) (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) (z : ℚ) :
    lengthBits (2*(mode L r N z).radius+1)≤radiusLogCoefficient C*ℓ := by
  have hR := mode_radius_polynomial hL0 hℓ hL hr hN z
  have h1 : 1≤ℓ^11 := one_le_pow₀ (by omega)
  have hradius : 2*(mode L r N z).radius+1≤(2*radiusCoefficient C+1)*ℓ^11 := by
    nlinarith only [hR,h1]
  simpa only [radiusLogCoefficient,show 2*radiusCoefficient C+1+1=2*radiusCoefficient C+2 by omega] using
    lengthBits_polynomial hℓ 11 hradius

theorem mode_frequency_polynomial {L r N C ℓ : ℕ} (hL0 : 0<L) (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) (z : ℚ) :
    templateFrequencyBound (size L r N) (L : ℚ) (mode L r N z).radius≤
      outputFrequencyCoefficient C*ℓ^8 := by
  rcases parameters_linear hℓ hL hr hN with ⟨_,_,hn,_,hb,hw,hk,_⟩
  have hc : C≤linearCoefficient C := by unfold linearCoefficient; omega
  exact mode_frequency_bound hL0 r N (linearCoefficient C) ℓ z hℓ
    (hL.trans (Nat.mul_le_mul_right _ hc)) hw hb hk hn

def outputArithmeticCoefficient (C : ℕ) : ℕ :=
  C+2+2*lengthCoefficient (C+2)+3*rootLogCoefficient (C+2)+
    3*radiusLogCoefficient (C+2)+outputFrequencyCoefficient (C+2)+32

theorem output_precisions_linear {L r N C ℓ : ℕ} (hL0 : 0<L) (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) (z : ℚ) :
    compactTensorBits N (lengthBits L) (outputSupportBits L r N z)≤outputArithmeticCoefficient C*ℓ ∧
    compactFourierBits N (lengthBits (size L r (N+2))) (outputSupportBits L r N z)≤
      outputArithmeticCoefficient C*ℓ ∧
    compactMassBits (outputSupportBits L r N z)≤outputArithmeticCoefficient C*ℓ := by
  have hL' : L≤(C+2)*ℓ^6 := hL.trans (Nat.mul_le_mul_right _ (by omega))
  have hr' : r≤(C+2)*ℓ^7 := hr.trans (Nat.mul_le_mul_right _ (by omega))
  have hN' : N+2≤(C+2)*ℓ := by nlinarith only [hN,hℓ]
  have hl : lengthBits L≤lengthCoefficient (C+2)*ℓ := lengthBits_polynomial hℓ 6 hL'
  have hm' := rootBits_linear hℓ hL' hr' hN'
  have hm : lengthBits (size L r (N+2))≤rootLogCoefficient (C+2)*ℓ := by
    unfold rootBits at hm'
    omega
  have hR : outputSupportBits L r N z≤radiusLogCoefficient (C+2)*ℓ :=
    mode_support_logarithm hL0 hℓ hL' hr' hN' z
  unfold compactTensorBits compactFourierBits compactMassBits outputArithmeticCoefficient
  constructor
  · nlinarith only [hN,hl,hR,hℓ]
  constructor
  · nlinarith only [hN,hm,hR,hℓ]
  · nlinarith only [hR,hℓ]

theorem output_frequency_polynomial {L r N C ℓ : ℕ} (hL0 : 0<L) (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) (z : ℚ) :
    templateFrequencyBound (size L r (N+2)) (L : ℚ) (mode L r (N+2) z).radius≤
      outputArithmeticCoefficient C*ℓ^8 := by
  have hL' : L≤(C+2)*ℓ^6 := hL.trans (Nat.mul_le_mul_right _ (by omega))
  have hr' : r≤(C+2)*ℓ^7 := hr.trans (Nat.mul_le_mul_right _ (by omega))
  have hN' : N+2≤(C+2)*ℓ := by nlinarith only [hN,hℓ]
  apply (mode_frequency_polynomial hL0 hℓ hL' hr' hN' z).trans
  apply Nat.mul_le_mul_right
  unfold outputArithmeticCoefficient
  omega

theorem outputTemplateBits_polynomial {L r N C ℓ : ℕ} (hL0 : 0<L) (hℓ : 0<ℓ)
    (hL : L≤C*ℓ^6) (hr : r≤C*ℓ^7) (hN : N≤C*ℓ) (z : ℚ)
    (hv : ‖(mode L r (N+2) z).value‖≤2) :
    (outputTemplateBits L r N z).length≤
      realCompactBitsCoefficient (outputArithmeticCoefficient C)*ℓ^25 := by
  have hp := output_precisions_linear hL0 hℓ hL hr hN z
  exact compactOutputBits_polylog (size L r (N+2)) (L : ℚ) (mode L r (N+2) z) N
    (lengthBits (size L r (N+2))) (outputSupportBits L r N z) (lengthBits L)
    (outputArithmeticCoefficient C) ℓ hv (lengthBits_bound _) hℓ
    (output_frequency_polynomial hL0 hℓ hL hr hN z) hp.1 hp.2.1 hp.2.2

#print axioms mode_support_logarithm
#print axioms outputTemplateBits_polynomial

end Maxwell.Continuum.Calibration.FiniteAlgorithm
