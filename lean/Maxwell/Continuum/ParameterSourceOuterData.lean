import Maxwell.Continuum.ParameterSourceOuterRelocation
import Maxwell.Continuum.ParameterSourceBudgetSpec
import Maxwell.Source.Nonzero

/-! Identify the search's executed integer operands with the mathematical
continuum parameter input, including the exact reciprocal error budget. -/
noncomputable section
namespace Maxwell.Continuum.Parameters.SourceOuter
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RoutingPorts.Complete
open Maxwell.Composition Maxwell.Logical
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def data (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz) (e : ℕ) : OuterMachine.Data :=
  ⟨2^e,S.nnz,Fintype.card (SourceDecoration.Vertex S (SelectedInput.input p S hm).precision),
    sourceBudgetNat p S hm,1,1,sourceErrorDen p S hm,
    fun _=>2^54*129*PhysicalParameters.routingSide S (SelectedInput.input p S hm).precision⟩

theorem initial_fields (κ η e : ℕ) (S : Source.SparseSystem) (precision : ℕ) :
    initial κ η e S precision 2200=inputLog S.nnz ∧
    initial κ η e S precision 2201=minimumLengthExponent e := by
  have fields:=SourcePrepare.fields κ η e S.n S.nnz (sourceCircuit S precision).size
    (SourcePhase.side S precision) (Fintype.card (SourceDecoration.Vertex S precision))
  constructor
  · simpa only [initial,SourceExecution.values,
      show (2200:ℕ)∈SourcePrepare.ports by decide,ite_true] using fields.1
  · simpa only [initial,SourceExecution.values,
      show (2201:ℕ)∈SourcePrepare.ports by decide,ite_true] using fields.2.1

theorem data_positive (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz) (e : ℕ) :
    (data p S hm e).Positive := by
  refine ⟨hm,?_,by change 0<(1:ℕ);decide,by change 0<(1:ℕ);decide,sourceErrorDen_pos p S hm⟩
  have positive:=(sourceInput p S hm).K_pos
  rw [source_K_eq] at positive
  exact_mod_cast positive

theorem data_initial (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) (e : ℕ) :
    OuterMachine.dataOf (initial ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e S
      (SelectedInput.input p S hm).precision)=data p S hm e := by
  let precision:=(SelectedInput.input p S hm).precision
  have fields:=SourcePrepare.fields ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e
    S.n S.nnz (sourceCircuit S precision).size (SourcePhase.side S precision)
    (Fintype.card (SourceDecoration.Vertex S precision))
  dsimp only at fields
  have condition : SourceBudgetMachine.condition S.nnz (sourceCircuit S precision).size
      (SourcePhase.side S precision) ⌈p.conditionExponent⌉₊=sourceBudgetNat p S hm :=
    SourceBudgetMachine.condition_source p S hm
  have error : SourceBudgetMachine.errorDen S.n S.nnz (sourceCircuit S precision).size
      (SourcePhase.side S precision) ⌈p.accuracyExponent⌉₊=sourceErrorDen p S hm :=
    SourceBudgetMachine.error_source p S hm hn hm2
  have keep (i : ℕ) (hi : i∈SourcePrepare.ports) :
      initial ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e S precision i=
        SourcePrepare.values ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e S.n S.nnz
          (sourceCircuit S precision).size (SourcePhase.side S precision)
          (Fintype.card (SourceDecoration.Vertex S precision)) i := by
    simp only [initial,ite_eq_left hi,SourceExecution.values]
  unfold OuterMachine.dataOf data
  congr 1
  · exact (keep 2210 (by decide)).trans fields.2.2.1
  · exact (keep 2211 (by decide)).trans fields.2.2.2.1
  · exact (keep 2212 (by decide)).trans fields.2.2.2.2.1
  · exact (keep 2213 (by decide)).trans (fields.2.2.2.2.2.1.trans condition)
  · exact (keep 2214 (by decide)).trans fields.2.2.2.2.2.2.1
  · exact (keep 2215 (by decide)).trans fields.2.2.2.2.2.2.2.1
  · exact (keep 2216 (by decide)).trans (fields.2.2.2.2.2.2.2.2.1.trans error)
  · funext j
    fin_cases j
    all_goals exact (keep _ (by decide)).trans (fields.2.2.2.2.2.2.2.2.2 _ (by decide))

theorem data_input (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz) (e : ℕ) :
    (data p S hm e).input (data_positive p S hm e)=sourceInput p S hm := by
  have hK:=source_K_eq p S hm
  have hE:=source_epsilon_eq p S hm
  unfold OuterMachine.Data.input data sourceInput
  congr 1
  · simpa only [sourceInput,Nat.cast_one,div_one] using hK.symm
  · simpa only [sourceInput,Nat.cast_one] using hE.symm

#print axioms data_initial
#print axioms data_input
end Maxwell.Continuum.Parameters.SourceOuter
