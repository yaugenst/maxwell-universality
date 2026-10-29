import Maxwell.Composition.SelectedLogicalBounds

/-! The actual selected separation is logarithmic and both physical scales
have fixed literal inverse-polynomial exponents. -/
noncomputable section
namespace Maxwell.Composition.SelectedSpacingBounds
open Maxwell.Realization Maxwell.Composition.SelectedLogicalBounds
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000

def platform (R : SelectedPlatform) : SpacingPlatform := PhysicalParameters.spacingPlatform R.physical
def weightExponent (R : SelectedPlatform) : ℕ :=
  constantExponent (platform R).weight (platform R).weight_pos
def budgetExponent (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  weightExponent R+logicalExponent p+errorExponent p
def distanceBase (R : SelectedPlatform) : ℕ := (platform R).spacingBase 0
def distanceSlope (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  (platform R).spacingSlope (budgetExponent p R)
def zetaExponent (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  (platform R).zetaExponent 0 (budgetExponent p R)
def alphaExponent (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  (platform R).alphaExponent 0 (budgetExponent p R)
def detuningExponent (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  R.physical.constants.detuningExponent (zetaExponent p R)

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (R : SelectedPlatform)
local notation "I" => SelectedInput.input p S hm

theorem budget_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    ((I).epsilon/((platform R).weight*(I).logicalBudget))⁻¹ ≤
      (2:ℚ)^0*(S.nnz:ℚ)^budgetExponent p R := by
  have hw := constant_le_input_power (platform R).weight (platform R).weight_pos S.nnz hm2
  have hK := logical_bound p S hm hm2 hunit
  have he := error_inverse_bound p S hm hm2 hunit
  have hK0 : (0:ℚ) ≤ (I).logicalBudget := (by norm_num : (0:ℚ) ≤ 1).trans (I).logicalBudget_ge_one
  have h := mul_bound _ _ _ (mul_bound _ _ _ hw hK hK0) he
    (inv_nonneg.mpr (I).epsilon_pos.le)
  rw [inv_div, div_eq_mul_inv, pow_zero, one_mul]
  exact h

theorem distance_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (I).distance R ≤ distanceBase R+distanceSlope p R*Nat.clog 2 S.nnz := by
  exact (platform R).spacing_le_clog (I).logicalBudget (I).epsilon
    (lt_of_lt_of_le zero_lt_one (I).logicalBudget_ge_one) (I).epsilon_pos
    S.nnz 0 (budgetExponent p R) (budget_bound p S hm R hm2 hunit)

theorem scales_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    ((I).zeta R)⁻¹ ≤ (S.nnz:ℚ)^zetaExponent p R ∧
      ((I).alpha R)⁻¹ ≤ (S.nnz:ℚ)^alphaExponent p R := by
  exact (platform R).selected_scales_literal (I).logicalBudget (I).epsilon
    (lt_of_lt_of_le zero_lt_one (I).logicalBudget_ge_one) (I).epsilon_pos
    S.nnz 0 (budgetExponent p R) hm2 (budget_bound p S hm R hm2 hunit)

theorem detuning_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (PhysicalGram.width R.physical ((I).zeta R) ((I).zeta_pos R))⁻¹ ≤
      (S.nnz:ℚ)^detuningExponent p R :=
  R.physical.constants.detuningWidth_inverse_literal ((I).zeta R) ((I).zeta_pos R)
    ((I).zeta_one R) S.nnz (zetaExponent p R) hm2 (scales_bound p S hm R hm2 hunit).1

end Maxwell.Composition.SelectedSpacingBounds
