import Maxwell.Continuum.ParameterSourceWidths

/-! Source-specialized running time for the executed budget preparation. -/
noncomputable section
namespace Maxwell.Continuum.Parameters.SourcePrepare
open Maxwell.Cost.RoutingPorts.Complete Maxwell.Composition

def sourceCostCoefficient (p : Source.Parameters) (e : ℕ) : ℕ :=
  costCoefficient ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e*(sourceOperandCoefficient p)^2

theorem source_cost (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hm2 : 2≤S.nnz) (hunit : IsUnit (Source.realMatrix S)) (e : ℕ) :
    cost ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e S.n S.nnz
      (Maxwell.Logical.sourceCircuit S (SelectedInput.input p S hm).precision).size
      (SourcePhase.side S (SelectedInput.input p S hm).precision) (sourceInput p S hm).J≤
        sourceCostCoefficient p e*(inputLog S.nnz)^2 := by
  apply (cost_quadratic _ _ _ _ _ _ _ _).trans
  have width:=Nat.pow_le_pow_left (source_operand_width p S hm hm2 hunit) 2
  calc
    _≤costCoefficient ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e*
        (sourceOperandCoefficient p*inputLog S.nnz)^2:=Nat.mul_le_mul_left _ width
    _=_:=by unfold sourceCostCoefficient;rw [mul_pow];ring

#print axioms source_cost
end Maxwell.Continuum.Parameters.SourcePrepare
