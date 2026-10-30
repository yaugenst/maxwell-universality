import Maxwell.Continuum.CalibrationFiniteAlgorithm
import Maxwell.Continuum.CalibrationSupercellRealization

/-! The operator used by the executable finite iteration approximates
the literal continuum auxiliary power operator at the selected work
precision. All geometry, inverse, cutoff, and periodization conditions
are discharged by the computed integer parameters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration.FiniteAlgorithm

open FreeFiber EffectiveMass MasterConstants Supercell

attribute [local irreducible] Sh powerOperator powerScale roundedSandwich physicalLift
  rootDegree computedRootConvolution size precision workPrecision

private def selectedOperator (A : FieldL2 →L[ℂ] FieldL2) : FieldL2 →L[ℂ] FieldL2 := A

private theorem selectedOperator_eq (A : FieldL2 →L[ℂ] FieldL2) : selectedOperator A=A := rfl

def auxiliaryOperator (L r N : ℕ) (z : ℚ) (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    FieldL2 →L[ℂ] FieldL2 :=
  selectedOperator (physicalLift (size L r N) (roundedSandwich (size L r N) (scale L r N) z 0 D
    (by norm_num) (by norm_num; positivity)
    (precision L r N) (rootBits L r N) (inverseSteps L r N) (cutoffBits L r N)))

private def scaledOperator (c : ℂ) (A : FieldL2 →L[ℂ] FieldL2) : FieldL2 →L[ℂ] FieldL2 := c • A

private theorem scaledOperator_eq (c : ℂ) (A : FieldL2 →L[ℂ] FieldL2) :
    scaledOperator c A=c • A := rfl

def computedOperator (L r N : ℕ) (z : ℚ) (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    FieldL2 →L[ℂ] FieldL2 :=
  scaledOperator (operatorScale L : ℂ) (auxiliaryOperator L r N z D)

theorem scale_cast (L r N : ℕ) :
    (scale L r N : ℝ)=2*(size L r N : ℝ)/(L : ℝ) := by
  simp only [scale,torusScale,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast]

private theorem operator_error_transport (A B S : FieldL2 →L[ℂ] FieldL2) {ε : ℝ}
    (hAB : A=B) (hB : ‖B-S‖ ≤ ε) : ‖A-S‖ ≤ ε := by
  rw [hAB]
  exact hB

private theorem selected_precision_guard (n ell k : ℕ) :
    cutoffWorkBits (n+96+1) ell ≤ n+2*ell+4*k+256 := by
  unfold cutoffWorkBits
  omega

private theorem drop_geometry_radius (x y r : ℝ) (hr : 0≤r)
    (h : 16*(x+r+1)≤y) : 16*(x+1)≤y := by linarith

theorem size_well_geometry (L r N : ℕ) :
    16*((L : ℝ)+1)≤(size L r N : ℝ) :=
  drop_geometry_radius L (size L r N) r (Nat.cast_nonneg r) (size_geometry L r N)

theorem selected_inverse_steps_lower (L r N : ℕ) :
    aliasSteps (precision L r N+2) (lengthBits L) ≤ inverseSteps L r N := by
  unfold inverseSteps
  exact le_rfl

theorem selected_cutoff_bits_lower (L r N : ℕ) :
    cutoffWorkBits (precision L r N) (lengthBits L) ≤ cutoffBits L r N := by
  unfold cutoffBits
  exact le_rfl

theorem selected_operator_precision (L r N : ℕ) :
    cutoffWorkBits (workPrecision N+96+1) (lengthBits L) ≤ precision L r N := by
  simpa only [precision] using selected_precision_guard (workPrecision N) (lengthBits L) (rootBits L r N)

theorem raw_auxiliaryOperator_error {L : ℕ} (hL : Ls ≤ (L : ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    ‖physicalLift (size L r N) (roundedSandwich (size L r N) (scale L r N) z 0 D
      (by norm_num) (by norm_num; positivity)
      (precision L r N) (rootBits L r N) (inverseSteps L r N) (cutoffBits L r N))-Sh D‖ ≤
      (1/2 : ℝ)^(workPrecision N+96) := by
  have hL0 : 0<L := by exact_mod_cast length_pos hL
  exact roundedSandwich_physical_error (size L r N) hL (scale L r N) z
    (scale_lower hL0 r N) D (size_even L r N) (size_well_geometry L r N)
    (scale_cast L r N) (workPrecision N+96) (precision L r N) (rootBits L r N)
    (lengthBits L) (inverseSteps L r N) (cutoffBits L r N)
    (scale_bound hL0 r N) (lengthBits_bound L) (selected_operator_precision L r N)
    (selected_inverse_steps_lower L r N) (selected_cutoff_bits_lower L r N) (size_accuracy L r N)

theorem auxiliaryOperator_eq (L r N : ℕ) (z : ℚ) (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    auxiliaryOperator L r N z D=
      physicalLift (size L r N) (roundedSandwich (size L r N) (scale L r N) z 0 D
        (by norm_num) (by norm_num; positivity)
        (precision L r N) (rootBits L r N) (inverseSteps L r N) (cutoffBits L r N)) :=
  selectedOperator_eq _

theorem auxiliaryOperator_error {L : ℕ} (hL : Ls ≤ (L : ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    ‖auxiliaryOperator L r N z D-Sh D‖ ≤ (1/2 : ℝ)^(workPrecision N+96) :=
  operator_error_transport _ _ _ (auxiliaryOperator_eq L r N z D)
    (raw_auxiliaryOperator_error hL r N z D)

theorem operatorScale_cast (L : ℕ) : (operatorScale L : ℝ)=powerScale (L : ℝ)⁻¹ := by
  rw [operatorScale,powerScale]
  push_cast
  rw [div_eq_mul_inv,inv_pow]

theorem physicalLift_smul (M : ℕ) [NeZero M] (c : ℂ)
    (T : FiberSpace →L[ℂ] FiberSpace) : physicalLift M (c • T)=c • physicalLift M T := by
  apply ContinuousLinearMap.ext
  intro f
  rw [physicalLift,physicalLift]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,map_smul]

theorem operatorScale_complex (L : ℕ) :
    (operatorScale L : ℂ)=((powerScale ((L : ℝ)⁻¹) : ℝ) : ℂ) := by
  rw [← operatorScale_cast]
  norm_cast

theorem computedOperator_unfold (L r N : ℕ) (z : ℚ) (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    computedOperator L r N z D=(operatorScale L : ℂ) • auxiliaryOperator L r N z D := by
  exact scaledOperator_eq (operatorScale L : ℂ) (auxiliaryOperator L r N z D)

theorem computedOperator_eq (L r N : ℕ) (z : ℚ) (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    computedOperator L r N z D=(powerScale (L : ℝ)⁻¹ : ℂ) • auxiliaryOperator L r N z D := by
  exact (computedOperator_unfold L r N z D).trans
    (congrArg (fun c : ℂ => c • auxiliaryOperator L r N z D) (operatorScale_complex L))

private theorem scalar_operator_bound (T S : FieldL2 →L[ℂ] FieldL2) (c : ℝ)
    {ε : ℝ} (hc : 0 ≤ c) (hTS : ‖T-S‖ ≤ ε) :
    ‖(c : ℂ) • T-(c : ℂ) • S‖ ≤ c*ε := by
  rw [← smul_sub (c : ℂ) T S,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left hTS hc

private theorem power_error_transport (A B T S : FieldL2 →L[ℂ] FieldL2) (c : ℝ) {ε : ℝ}
    (hA : A=(c : ℂ) • T) (hB : B=(c : ℂ) • S) (hc : 0 ≤ c) (he : ‖T-S‖ ≤ ε) :
    ‖A-B‖ ≤ c*ε := by
  rw [hA,hB]
  exact scalar_operator_bound T S c hc he

theorem computedOperator_error {L : ℕ} (hL : Ls ≤ (L : ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    ‖computedOperator L r N z D-powerOperator D‖ ≤ (1/2 : ℝ)^workPrecision N := by
  have hc0 := powerScale_pos D.h_pos
  have hc : powerScale (L : ℝ)⁻¹ ≤ (2 : ℝ)^90 := by
    rw [powerScale]
    have hi : (L : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (length_ge_one hL)
    have hsq : ((L : ℝ)⁻¹)^2 ≤ 1 := by nlinarith [D.h_pos]
    exact (mul_le_mul_of_nonneg_left hsq (by positivity)).trans_eq (mul_one _)
  have hbound := power_error_transport (computedOperator L r N z D) (powerOperator D)
    (auxiliaryOperator L r N z D) (Sh D) (powerScale ((L : ℝ)⁻¹))
    (computedOperator_eq L r N z D) (by unfold powerOperator; rfl) hc0.le
    (auxiliaryOperator_error hL r N z D)
  apply hbound.trans
  calc
    _ ≤ (2 : ℝ)^90*(1/2 : ℝ)^(workPrecision N+96) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (1/2 : ℝ)^workPrecision N*((2 : ℝ)^90*(1/2 : ℝ)^96) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) (by norm_num)

#print axioms auxiliaryOperator_error
#print axioms computedOperator_error

end Maxwell.Continuum.Calibration.FiniteAlgorithm
