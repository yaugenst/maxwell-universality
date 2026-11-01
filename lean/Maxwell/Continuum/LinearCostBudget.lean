import Maxwell.Continuum.Main

/-! Source-linear bit costs fit the common quantitative budget. -/
noncomputable section
namespace Maxwell.Continuum.Realization

theorem linear_cost_budget (C : Constants) (S : Source.SparseSystem) (A cost k r : ℕ)
    (hC : 2*A≤C.overhead) (hk : k≤r)
    (hc : cost≤A*(S.nnz+1)*(Parameters.inputLog S.nnz)^k) :
    (cost:ℝ)≤budget C S r := by
  have hm : 1≤S.effectiveSize := (by decide : 1≤2).trans (le_max_left _ _)
  have hl : 1≤Parameters.inputLog S.nnz:=Parameters.inputLog_pos S.nnz
  have hs : S.nnz+1≤2*S.effectiveSize := by
    have h:=le_max_right 2 S.nnz
    unfold Source.SparseSystem.effectiveSize at *
    omega
  have hnat : cost≤(2*A)*S.effectiveSize*(Parameters.inputLog S.nnz)^k :=
    hc.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A hs)).trans_eq (by ring))
  have hmR : (1:ℝ)≤S.effectiveSize:=by exact_mod_cast hm
  have hlR : (1:ℝ)≤Parameters.inputLog S.nnz:=by exact_mod_cast hl
  have power : (S.effectiveSize:ℝ)≤(S.effectiveSize:ℝ)^(3/2:ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hmR (by norm_num : (1:ℝ)≤3/2)
  have coef : ((2*A:ℕ):ℝ)≤C.overhead:=by exact_mod_cast hC
  calc
    (cost:ℝ)≤((2*A:ℕ):ℝ)*(S.effectiveSize:ℝ)*(Parameters.inputLog S.nnz:ℝ)^k:=by exact_mod_cast hnat
    _≤(C.overhead:ℝ)*(S.effectiveSize:ℝ)^(3/2:ℝ)*(Parameters.inputLog S.nnz:ℝ)^r:=by
      gcongr
    _=budget C S r:=rfl

#print axioms linear_cost_budget
end Maxwell.Continuum.Realization
