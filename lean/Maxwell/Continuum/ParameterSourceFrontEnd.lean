import Maxwell.Continuum.ParameterSourceExecution

/-! The fixed front end begins on the original source bytes. The width
certificate below is derived by the source compiler, not supplied to code. -/
noncomputable section
namespace Maxwell.Continuum.Parameters.SourceFrontEnd
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RoutingPorts.Complete
open Maxwell.Composition
set_option maxRecDepth 20000
set_option maxHeartbeats 2600000

def code (κ η e : ℕ) : Code := .seq (SourceGraph.Incidence.code κ η) (SourceExecution.code κ η e)

theorem executes (p : Source.Parameters) (S : Source.SparseSystem) (hp : Source.Promises p S)
    (hm : 2≤S.nnz) (hb : S.source≠0) (e : ℕ) (tape : ℕ→Bool) :
    let κ:=⌈p.conditionExponent⌉₊
    let η:=⌈p.accuracyExponent⌉₊
    let precision:=Maxwell.Realization.binaryCoefficientPrecision S.nnz κ η
    ∃room : SourceGraph.Positive.dimension S precision<2^SourceGraph.Positive.width S precision,
      ∃steps t,Executes (Codec.source S) tape (code κ η e) steps (Store.ofState BitRAMState.initial) t ∧
        steps≤SourceGraph.Incidence.totalBudget p S κ η+SourceExecution.cost κ η e S precision room ∧
        SourceExecution.Result κ η e S precision t ∧
        t.val.inputHead=(Codec.source S).length ∧ t.val.randomCursor=0 ∧ t.val.output=[] := by
  dsimp only
  obtain ⟨c₀,s,e₀,h₀,hs⟩:=SourceGraph.Incidence.executes p S hp hm hb
    ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ tape
  obtain ⟨c₁,t,e₁,h₁,rt,frame,_⟩:=SourceExecution.executes ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e
    S _ hm (Codec.source S) tape s hs
  have io:=hs.io
  exact ⟨hs.room,c₀+c₁,t,e₀.seq e₁,Nat.add_le_add h₀ h₁,rt,
    frame.inputHead.trans io.1,frame.randomCursor.trans io.2.1,frame.output.trans io.2.2⟩

#print axioms executes
end Maxwell.Continuum.Parameters.SourceFrontEnd
