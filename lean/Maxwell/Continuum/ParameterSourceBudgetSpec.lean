import Maxwell.Continuum.ParameterSourceBudgetMachine

namespace Maxwell.Continuum.Parameters.SourceBudgetMachine
open Maxwell.Composition Maxwell.Logical
set_option maxHeartbeats 1200000

theorem condition_source (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz) :
    condition S.nnz (sourceCircuit S (SelectedInput.input p S hm).precision).size
      (PhysicalParameters.routingSide S (SelectedInput.input p S hm).precision) ⌈p.conditionExponent⌉₊=
      sourceBudgetNat p S hm := rfl

theorem error_source (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) :
    errorDen S.n S.nnz (sourceCircuit S (SelectedInput.input p S hm).precision).size
      (PhysicalParameters.routingSide S (SelectedInput.input p S hm).precision) ⌈p.accuracyExponent⌉₊=
      sourceErrorDen p S hm := by
  let precision:=(SelectedInput.input p S hm).precision
  have hr : 1≤PhysicalAccuracy.residualFactor S precision := routedResidualFactor_pos S hn precision _
  have hmSquare : 1≤S.nnz^2 := Nat.one_le_pow _ _ hm
  have hd : S.nnz^2≤PhysicalAccuracy.denominator S precision := by
    rw [PhysicalAccuracy.denominator,max_eq_right hr,max_eq_right hmSquare]
    exact Nat.le_mul_of_pos_left _ hr
  have hp : 1≤S.nnz^⌈p.accuracyExponent⌉₊ := Nat.one_le_pow _ _ hm
  have hlarge : 2≤S.nnz^⌈p.accuracyExponent⌉₊*PhysicalAccuracy.denominator S precision := by
    have hs : 2≤S.nnz^2 := by nlinarith
    exact hs.trans (hd.trans (Nat.le_mul_of_pos_left _ hp))
  rw [sourceErrorDen,max_eq_right hlarge]
  change 1≤PhysicalAccuracy.residualFactor S (SelectedInput.input p S hm).precision at hr
  rw [PhysicalAccuracy.denominator,max_eq_right hr,max_eq_right hmSquare]
  simp only [errorDen,
    PhysicalAccuracy.residualFactor,routedResidualFactor,positiveResidualFactor]
  ring

#print axioms condition_source
#print axioms error_source
end Maxwell.Continuum.Parameters.SourceBudgetMachine
