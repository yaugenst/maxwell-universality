import Maxwell.Continuum.ParameterStage
import Maxwell.Cost.SelectedParameters.GeometricCeiling

/-! The detuning budget is a reciprocal integer. Its actual least dyadic
precision is therefore the binary logarithmic ceiling of that integer. -/
namespace Maxwell.Continuum.Parameters.OuterTau
open Maxwell.Cost.SelectedParameters
set_option maxHeartbeats 1000000

def budgetDen (L d : ℕ) : ℕ := 2^24*L^4*(3^d)^2

theorem budgetDen_pos (L d : ℕ) (hL : 0<L) : 0<budgetDen L d := by unfold budgetDen;positivity

theorem budget_eq (L d : ℕ) : tauBudget L d=1/(budgetDen L d:ℚ) := by
  simp only [tauBudget,budgetDen,zeta,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [show (1/3:ℚ)=(3:ℚ)⁻¹ by norm_num]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow,one_mul]

theorem precision_eq (L d : ℕ) (hL : 0<L) :
    Realization.precisionBits (tauBudget L d) (tauBudget_pos hL d)=Nat.clog 2 (budgetDen L d) := by
  unfold Realization.precisionBits
  simp only [Realization.precisionBudget,min_eq_right (tauBudget_le_one hL d)]
  have hden := budgetDen_pos L d hL
  have he := Geometric.exponent_eq_clog 2 (budgetDen L d) (by decide) hden
  unfold Geometric.exponent at he
  simpa only [Nat.cast_one,Nat.cast_ofNat,← budget_eq L d] using he

theorem tau_eq (L d : ℕ) (hL : 0<L) :
    tau L d hL=1/(2:ℚ)^(Nat.clog 2 (budgetDen L d)) := by
  rw [tau,Realization.precisionUnit,precision_eq L d hL]

#print axioms tau_eq
end Maxwell.Continuum.Parameters.OuterTau
