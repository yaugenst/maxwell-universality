import Maxwell.Continuum.ContinuumRealizationResources
import Maxwell.Continuum.CalibrationFiniteResources
import Maxwell.Continuum.CalibrationPlacementRadius

/-! Source-specialized resources for the actual finite continuum
calibration, including all three useful-coupling displacement radii. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.RealizationParameters

open Calibration
attribute [local irreducible] Parameters.sourceMagnitude MasterConstants.exponent
  Parameters.sourceInput

def calibrationBaseCoefficient (p : Source.Parameters) : ℕ :=
  2^(6+45*Parameters.sourceMagnitude p)+2^(9*Parameters.sourceMagnitude p)+outputBitCoefficient p

def calibrationInputCoefficient (p : Source.Parameters) : ℕ :=
  calibrationBaseCoefficient p+2^53*(calibrationBaseCoefficient p)^2+
    (outputBitCoefficient p+2*(Nat.clog 2 (calibrationBaseCoefficient p+1)+6)+8)

def calibrationModePrecision (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz) : ℕ :=
  calibrationPrecision p S hm+2*lengthBits (length p S hm)+8

def calibrationRadius (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz) : ℕ :=
  couplingRadius (length p S hm) (spacing p S hm)

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
  (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S))

include hm2 hu

theorem calibration_base_scales :
    length p S hm≤calibrationBaseCoefficient p*(logSize S)^6 ∧
    spacing p S hm≤calibrationBaseCoefficient p*logSize S ∧
    calibrationPrecision p S hm≤outputBitCoefficient p*logSize S := by
  have hs := Parameters.source_scales p S hm hm2 hu
  have hL : length p S hm≤2^(6+45*Parameters.sourceMagnitude p)*(logSize S)^6 := hs.1
  have hd : spacing p S hm≤2^(9*Parameters.sourceMagnitude p)*logSize S := hs.2.1
  refine ⟨hL.trans (Nat.mul_le_mul_right _ ?_),hd.trans (Nat.mul_le_mul_right _ ?_),
    (selected_precisions_linear p S hm hm2 hu).2.2.2.2.2.1⟩
  · exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  · exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)

theorem calibration_inputs_polynomial :
    length p S hm≤calibrationInputCoefficient p*(logSize S)^6 ∧
    calibrationRadius p S hm≤calibrationInputCoefficient p*(logSize S)^7 ∧
    calibrationModePrecision p S hm≤calibrationInputCoefficient p*logSize S := by
  have hs := calibration_base_scales p S hm hm2 hu
  have hℓ := Parameters.inputLog_pos S.nnz
  have hr := couplingRadius_polynomial hs.1 hs.2.1
  have hlog := FiniteAlgorithm.lengthBits_polynomial hℓ 6 hs.1
  have hJ : calibrationModePrecision p S hm≤
      (outputBitCoefficient p+2*(Nat.clog 2 (calibrationBaseCoefficient p+1)+6)+8)*logSize S := by
    unfold calibrationModePrecision
    nlinarith only [hs.2.2,hlog,hℓ]
  refine ⟨hs.1.trans (Nat.mul_le_mul_right _ ?_),hr.trans (Nat.mul_le_mul_right _ ?_),
    hJ.trans (Nat.mul_le_mul_right _ ?_)⟩ <;> unfold calibrationInputCoefficient <;> omega

theorem selected_finite_inputs (N : ℕ) (hN : N≤outputBitCoefficient p*logSize S) :
    length p S hm≤calibrationInputCoefficient p*(logSize S)^6 ∧
    calibrationRadius p S hm≤calibrationInputCoefficient p*(logSize S)^7 ∧
    N≤calibrationInputCoefficient p*logSize S := by
  have hs := calibration_inputs_polynomial p S hm hm2 hu
  refine ⟨hs.1,hs.2.1,hN.trans (Nat.mul_le_mul_right _ ?_)⟩
  unfold calibrationInputCoefficient
  omega

theorem calibration_size_polynomial :
    FiniteAlgorithm.size (length p S hm) (calibrationRadius p S hm) (calibrationModePrecision p S hm)≤
      FiniteAlgorithm.sizeCoefficient (calibrationInputCoefficient p)*(logSize S)^8 := by
  have hs := calibration_inputs_polynomial p S hm hm2 hu
  exact FiniteAlgorithm.size_polynomial (Parameters.inputLog_pos S.nnz) hs.1 hs.2.1 hs.2.2

theorem calibration_parameters_linear :
    let L := length p S hm
    let r := calibrationRadius p S hm
    let N := calibrationModePrecision p S hm
    let C := FiniteAlgorithm.linearCoefficient (calibrationInputCoefficient p)
    N≤C*logSize S ∧ lengthBits L≤C*logSize S ∧
    FiniteAlgorithm.iterations N≤C*logSize S ∧ FiniteAlgorithm.workPrecision N≤C*logSize S ∧
    FiniteAlgorithm.rootBits L r N≤C*logSize S ∧ FiniteAlgorithm.precision L r N≤C*logSize S ∧
    FiniteAlgorithm.inverseSteps L r N≤C*logSize S ∧ FiniteAlgorithm.cutoffBits L r N≤C*logSize S := by
  have hs := calibration_inputs_polynomial p S hm hm2 hu
  exact FiniteAlgorithm.parameters_linear (Parameters.inputLog_pos S.nnz) hs.1 hs.2.1 hs.2.2

#print axioms calibration_size_polynomial
#print axioms calibration_parameters_linear

end Maxwell.Continuum.RealizationParameters
