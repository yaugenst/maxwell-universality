import Maxwell.Continuum.FourierTensorArithmeticWidth

/-! Literal tensor-machine parameters selected by the calibrated compact
template constructor, with their dimension and arithmetic bounds. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost RationalDataflow Calibration Calibration.FiniteAlgorithm Calibration.Supercell
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] MasterConstants.exponent FiniteAlgorithm.mode FiniteAlgorithm.size
  FiniteAlgorithm.sizeCoefficient FiniteAlgorithm.radiusCoefficient FiniteAlgorithm.outputArithmeticCoefficient

def outputArithmeticWidth (L r N : ℕ) (z : ℚ) : ℕ :=
  ModePrelude.arithmeticWidth (FiniteAlgorithm.size L r (N+2))
    (compactNormalizationBits N (lengthBits (FiniteAlgorithm.size L r (N+2)))) L
    (FiniteAlgorithm.mode L r (N+2) z).radius
    (compactFourierBits N (lengthBits (FiniteAlgorithm.size L r (N+2))) (outputSupportBits L r N z))
    (outputFrequency L r N z) (outputTensorPrecision L r N z)
    (compactMassBits (outputSupportBits L r N z))

def outputDimensionCoefficient (C : ℕ) : ℕ :=
  C+sizeCoefficient (C+2)+radiusCoefficient (C+2)+3*(2*radiusCoefficient (C+2)+1)^3+
    outputArithmeticCoefficient C+waveDegreeCoefficient (outputArithmeticCoefficient C)+
    waveGridCoefficient (outputArithmeticCoefficient C)+1

def outputWorkspaceCoefficient (C : ℕ) : ℕ := ModePrelude.arithmeticCoefficient (outputDimensionCoefficient C)
def outputAliasCoefficient (C : ℕ) : ℕ := (2*radiusCoefficient (C+2)+1)^3+1
def outputLoopCoefficient (C : ℕ) : ℕ := outputArithmeticCoefficient C+outputWorkspaceCoefficient C+64

theorem frequency_nat (M L R : ℕ) [NeZero M] :
    L*R≤2*M*templateFrequencyBound M (L:ℚ) R := by
  have h := templateFrequencyBound_spec M (L:ℚ) R
  rw [abs_of_nonneg (Nat.cast_nonneg L)] at h
  exact_mod_cast h

theorem outputParameters_frequency (L r N : ℕ) (z : ℚ) :
    L*(FiniteAlgorithm.mode L r (N+2) z).radius≤
      2*FiniteAlgorithm.size L r (N+2)*outputFrequency L r N z :=
  frequency_nat (FiniteAlgorithm.size L r (N+2)) L (FiniteAlgorithm.mode L r (N+2) z).radius

theorem outputParameters_mass (L r N : ℕ) (z : ℚ) :
    (6:ℝ)*RowArithmetic.rowCount (FiniteAlgorithm.mode L r (N+2) z).radius≤
      (2:ℝ)^compactMassBits (outputSupportBits L r N z) :=
  ModePrelude.row_mass (FiniteAlgorithm.mode L r (N+2) z).radius

theorem outputParameters_aliases {L r N C ell : ℕ} (hL0 : 0<L) (hell : 0<ell)
    (hL : L≤C*ell^6) (hr : r≤C*ell^7) (hN : N≤C*ell) (z : ℚ) :
    RowArithmetic.rowCount (FiniteAlgorithm.mode L r (N+2) z).radius+1≤outputAliasCoefficient C*ell^33 := by
  have hL' : L≤(C+2)*ell^6 := hL.trans (Nat.mul_le_mul_right _ (by omega))
  have hr' : r≤(C+2)*ell^7 := hr.trans (Nat.mul_le_mul_right _ (by omega))
  have hN' : N+2≤(C+2)*ell := by nlinarith only [hN,hell]
  have hs := ModePrelude.rowCount_polynomial hell (mode_radius_polynomial hL0 hell hL' hr' hN' z)
  have h1 : 1≤ell^33 := one_le_pow₀ hell
  unfold outputAliasCoefficient
  nlinarith only [hs,h1]

theorem outputParameters_work {L r N C ell : ℕ} (hL0 : 0<L) (hell : 0<ell)
    (hL : L≤C*ell^6) (hr : r≤C*ell^7) (hN : N≤C*ell) (z : ℚ) :
    outputArithmeticWidth L r N z≤outputWorkspaceCoefficient C*ell := by
  have hL' : L≤(C+2)*ell^6 := hL.trans (Nat.mul_le_mul_right _ (by omega))
  have hr' : r≤(C+2)*ell^7 := hr.trans (Nat.mul_le_mul_right _ (by omega))
  have hN' : N+2≤(C+2)*ell := by nlinarith only [hN,hell]
  have hm := size_polynomial hell hL' hr' hN'
  have hR := mode_radius_polynomial hL0 hell hL' hr' hN' z
  have hp := output_precisions_linear hL0 hell hL hr hN z
  have hq := output_frequency_polynomial hL0 hell hL hr hN z
  have hd := waveDegree_polylog hell hq hp.1
  have hg := waveGrid_polylog hell hq hp.1
  have hc := ModePrelude.aliasArraySize_polynomial hell hR
  have hn := ModePrelude.rowCount_polynomial hell hR
  have ha : compactNormalizationBits N (lengthBits (FiniteAlgorithm.size L r (N+2)))≤
      outputArithmeticCoefficient C*ell := by
    apply le_trans _ hp.2.1
    unfold compactNormalizationBits compactFourierBits
    omega
  have lift {x a k : ℕ} (hx : x≤a*ell^k) (ha : a≤outputDimensionCoefficient C) (hk : k≤33) :
      x≤outputDimensionCoefficient C*ell^33 :=
    hx.trans (Nat.mul_le_mul ha (Nat.pow_le_pow_right hell hk))
  have small (ha : outputArithmeticCoefficient C≤outputDimensionCoefficient C) {x : ℕ}
      (hx : x≤outputArithmeticCoefficient C*ell) : x≤outputDimensionCoefficient C*ell :=
    hx.trans (Nat.mul_le_mul_right _ ha)
  have hC : outputArithmeticCoefficient C≤outputDimensionCoefficient C := by
    unfold outputDimensionCoefficient;omega
  apply ModePrelude.arithmeticWidth_linear hell
  · exact lift hm (by unfold outputDimensionCoefficient;omega) (by decide)
  · exact small hC ha
  · exact lift hL (by unfold outputDimensionCoefficient;omega) (by decide)
  · exact lift hR (by unfold outputDimensionCoefficient;omega) (by decide)
  · exact lift hc (by unfold outputDimensionCoefficient;omega) le_rfl
  · exact lift hn (by unfold outputDimensionCoefficient;omega) le_rfl
  · exact small hC hp.2.1
  · exact hq.trans (Nat.mul_le_mul_right _ hC)
  · exact small hC hp.1
  · exact small hC hp.2.2
  · exact lift hd (by unfold outputDimensionCoefficient;omega) (by decide)
  · exact lift hg (by unfold outputDimensionCoefficient;omega) (by decide)

theorem outputParameters_loop {L r N C ell : ℕ} (hL0 : 0<L) (hell : 0<ell)
    (hL : L≤C*ell^6) (hr : r≤C*ell^7) (hN : N≤C*ell) (z : ℚ) :
    outputFrequency L r N z+outputTensorPrecision L r N z+outputArithmeticWidth L r N z+64≤
      (2*outputLoopCoefficient C)*ell^8 := by
  have hw := outputParameters_work hL0 hell hL hr hN z
  have hn := (output_precisions_linear hL0 hell hL hr hN z).1
  have hq := output_frequency_polynomial hL0 hell hL hr hN z
  have ep : ell≤ell^8 := Nat.le_self_pow (by decide) ell
  have en := hn.trans (Nat.mul_le_mul_left _ ep)
  have ew := hw.trans (Nat.mul_le_mul_left _ ep)
  have h1 : 1≤ell^8 := one_le_pow₀ hell
  change outputFrequency L r N z≤_ at hq
  change outputTensorPrecision L r N z≤_ at en
  unfold outputLoopCoefficient
  nlinarith only [hq,en,ew,h1,Nat.zero_le (outputWorkspaceCoefficient C*ell^8)]

#print axioms outputParameters_frequency
#print axioms outputParameters_work
#print axioms outputParameters_loop
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
