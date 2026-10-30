import Maxwell.Cost.SourceGraph.Asymptotics
import Maxwell.Cost.SourceGraph.Correctness
import Maxwell.Continuum.ContinuumRealizationParameters

/-! The actual fixed sparse-source frontend, specialized to the continuum
precision. Its graph arrays and original RHS archive are computed from the
input stream with the existing charged bit-work bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Cost Maxwell.Cost.Structured

def sourceFrontendCode (p : Source.Parameters) : Code :=
  SourceGraph.Positive.code ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊

def sourceFrontendBudget (p : Source.Parameters) (S : Source.SparseSystem) : ℕ :=
  SourceGraph.Positive.totalBudget p S ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊

theorem source_frontend_executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hm : 0<S.nnz) (hp : Source.Promises p S) (hm2 : 2≤S.nnz)
    (hb : S.source≠0) (tape : ℕ→Bool) :
    ∃cost t, Executes (Maxwell.Codec.source S) tape (sourceFrontendCode p) cost
        (Store.ofState BitRAMState.initial) t ∧
      cost≤sourceFrontendBudget p S ∧
      SourceGraph.Positive.Result S (precision p S hm) t ∧
      t.val.tapes 508=BitTape.ofList (LogRats.records (List.ofFn S.source)) ∧
      t.val.inputHead=(Maxwell.Codec.source S).length ∧
      t.val.randomCursor=0 ∧ t.val.output=[] := by
  obtain ⟨cost,t,he,hc,ht⟩ := SourceGraph.Positive.executes p S hp hm2 hb
    ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ tape
  exact ⟨cost,t,he,hc,ht,ht.data.rhs,ht.io⟩

theorem source_frontend_cost (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm2 : 2≤S.nnz) :
    (sourceFrontendBudget p S : ℝ)≤
      SourceGraph.Positive.runtimeFactor p ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊*
        (S.nnz : ℝ)*Real.log ((S.nnz : ℝ)+2)^4 :=
  SourceGraph.Positive.totalBudget_polylog p S hp hm2 _ _

#print axioms source_frontend_executes
#print axioms source_frontend_cost

end Maxwell.Continuum.RealizationParameters
