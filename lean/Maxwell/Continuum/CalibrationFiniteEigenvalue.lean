import Maxwell.Continuum.CalibrationFiniteMode
import Maxwell.Continuum.CalibrationEigenvalueInterval

/-! Executable rational intervals for the actual continuum auxiliary
eigenvalue, obtained from the computed Fourier mode and exact finite
rational quadratic sums. -/

set_option backward.isDefEq.respectTransparency true
namespace Maxwell.Continuum.Calibration.FiniteAlgorithm

open FreeFiber Supercell EffectiveMass MasterConstants

attribute [local irreducible] mode modeImage auxiliaryOperator size
  Sh realMode muH roundedSandwich

def enclosureModePrecision (L N : ℕ) : ℕ := N+2*lengthBits L+8

def modeInterval (L r N : ℕ) (z : ℚ) : RationalInterval :=
  couplingInterval (eigenvalueCenter L r (enclosureModePrecision L N) z) N

theorem modeInterval_width (L r N : ℕ) (z : ℚ) :
    (modeInterval L r N z).width=(1/2 : ℚ)^N := couplingInterval_width _ _

theorem modeImage_eq (L r N : ℕ) (z : ℚ) : modeImage L r N z =
    FourierData.sandwichApply (size L r N) (scale L r N) z 0
      (precision L r N) (rootBits L r N) (inverseSteps L r N) (cutoffBits L r N)
      (mode L r N z) := by
  unfold modeImage
  rfl

private theorem finite_value_transport (v w : FourierData) (u : FiberSpace)
    (hv : v=w) (hw : w.value=u) : v.value=u := by rw [hv]; exact hw

theorem modeImage_value {L : ℕ} (hL : Ls≤(L : ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    (modeImage L r N z).value =
      roundedSandwich (size L r N) (scale L r N) z 0 D (by norm_num) (by norm_num; positivity)
        (precision L r N) (rootBits L r N) (inverseSteps L r N) (cutoffBits L r N)
        (mode L r N z).value :=
  finite_value_transport _ _ _ (modeImage_eq L r N z)
    (FourierData.sandwichApply_value (size L r N) (length_ge_one hL)
      (scale L r N) z 0 D (by norm_num) (by norm_num; positivity)
      (precision L r N+2) (lengthBits L) (precision L r N) (rootBits L r N)
      (inverseSteps L r N) (cutoffBits L r N) (lengthBits_bound L)
      (selected_inverse_steps_lower L r N) (mode L r N z))

theorem physical_realInner (M : ℕ) [NeZero M] (v w : FourierData)
    (T : FiberSpace →L[ℂ] FiberSpace) (A : FieldL2 →L[ℂ] FieldL2)
    (hA : A=physicalLift M T) (hw : w.value=T v.value) :
    (v.realInner w : ℝ)=(inner ℂ (embedding M v.value) (A (embedding M v.value))).re := by
  rw [FourierData.realInner_eq,hA,physicalLift_apply,hw,(embedding M).inner_map_map]

theorem eigenvalueCenter_physical {L : ℕ} (hL : Ls≤(L : ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    (eigenvalueCenter L r N z : ℝ)=
      (inner ℂ (embedding (size L r N) (mode L r N z).value)
        (auxiliaryOperator L r N z D (embedding (size L r N) (mode L r N z).value))).re := by
  exact physical_realInner _ _ _ _ _ (auxiliaryOperator_eq L r N z D) (modeImage_value hL r N z D)

private theorem workPrecision_ge (N : ℕ) : N≤workPrecision N+96 := by
  unfold workPrecision powerWorkPrecision powerWorkBits targetPrecision
  omega

private theorem enclosure_precision_guard (N ell : ℕ) :
    cutoffWorkBits (N+1) ell≤N+2*ell+8 := by unfold cutoffWorkBits; omega

theorem modeInterval_contains {L : ℕ} (hL : Ls≤(L : ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    (modeInterval L r N z).Contains (muH D (inverse_length_le_1024 hL)) := by
  let J := enclosureModePrecision L N
  have hB : ‖auxiliaryOperator L r J z D-Sh D‖≤(1/2 : ℝ)^J :=
    (auxiliaryOperator_error hL r J z D).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (workPrecision_ge J))
  exact eigenvalue_interval hL D N (lengthBits L) J (lengthBits_bound L)
    (enclosure_precision_guard N (lengthBits L)) (auxiliaryOperator L r J z D)
    (embedding (size L r J) (mode L r J z).value) (eigenvalueCenter L r J z)
    (mode_physical_error hL r J z D) hB (eigenvalueCenter_physical hL r J z D)

#print axioms eigenvalueCenter_physical
#print axioms modeInterval_contains
end Maxwell.Continuum.Calibration.FiniteAlgorithm
