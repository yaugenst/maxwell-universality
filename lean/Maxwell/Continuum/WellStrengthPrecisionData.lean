import Maxwell.Continuum.FiniteAuxiliaryDyadicBits
import Maxwell.Cost.SelectedParameters.GeometricBounds

/-! The actual scalar-well budget is a reciprocal natural. This identity
lets the existing exact binary selector consume the computed length and
spacing power, without a supplied precision or execution witness. -/
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Realization Maxwell.Cost
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def precisionDenominator (L z : ℕ) : ℕ := 2*L^4*z^2

theorem scalar_budget (L d : ℕ) (hL : 0<L) :
    scalarBudget ((L:ℚ)⁻¹^2) (Parameters.zeta d) ((2:ℚ)^128*(L:ℚ)⁻¹^2)=
      1/(precisionDenominator L (3^d):ℚ) := by
  have positive : (0:ℚ)<L:=by exact_mod_cast hL
  have atLeastOne : (1:ℚ)≤L:=by exact_mod_cast hL
  have reciprocal : (L:ℚ)⁻¹≤1:=by
    simpa using (inv_le_one₀ positive).mpr atLeastOne
  have lower : (L:ℚ)⁻¹^2≤1:=pow_le_one₀ (by positivity) reciprocal
  have zeta : (Parameters.zeta d)^2≤1:=by
    apply pow_le_one₀ (by positivity [Parameters.zeta_pos d])
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have square : ((L:ℚ)⁻¹^2)^2≤(L:ℚ)⁻¹^2:=by nlinarith [sq_nonneg ((L:ℚ)⁻¹^2)]
  have middle : ((L:ℚ)⁻¹^2)^2*(Parameters.zeta d)^2/2≤(L:ℚ)⁻¹^2:=by
    have product:=mul_le_mul_of_nonneg_left zeta (sq_nonneg ((L:ℚ)⁻¹^2))
    nlinarith [sq_nonneg ((L:ℚ)⁻¹)]
  have reserve : ((L:ℚ)⁻¹^2)^2*(Parameters.zeta d)^2/2≤2*((2:ℚ)^128*(L:ℚ)⁻¹^2):=by
    apply middle.trans
    have factor : (1:ℚ)≤2*2^128:=by norm_num
    nlinarith [mul_le_mul_of_nonneg_right factor (sq_nonneg ((L:ℚ)⁻¹))]
  rw [scalarBudget,min_eq_left reserve,min_eq_right middle]
  simp only [precisionDenominator,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Parameters.zeta,div_pow,one_pow]
  field_simp

theorem selected_precision (L d : ℕ) (hL : 0<L) :
    SelectedParameters.Geometric.exponent 1 2 1 (precisionDenominator L (3^d))
      (by decide) (by decide) (by decide) (by unfold precisionDenominator;positivity)=
      FiniteAuxiliary.onsitePrecision L d hL := by
  rw [SelectedParameters.Geometric.binary_exponent]
  unfold FiniteAuxiliary.onsitePrecision
  congr 1
  exact (scalar_budget L d hL).symm

#print axioms selected_precision
end Maxwell.Continuum.WellStrengthInitialization
