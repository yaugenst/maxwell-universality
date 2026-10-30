import Maxwell.Continuum.SourceRoutingCursorStep
import Maxwell.Continuum.IndexedMeasuredLoop

/-! Complete fixed runtime sentinel scan. The proof charges at most two
cursor sweeps, including every branch, loop test, and final comparison. -/

namespace Maxwell.Cost.RoutingPorts.Complete
open Structured
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def cursorCode : Code := .seq (cursorTestCode 730) (.loop 2 cursorBodyCode)

def cursorCost {n : ℕ} (l : Layout n) : ℕ := (2*n+1)*(6*operationCap l+4)

theorem cursor_executes {n : ℕ} (l : Layout n) (p : CompletionPlan n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : CursorRuntime l p 0 0 0 s) :
    ∃cost t j, Executes input tape cursorCode cost s t ∧ cost≤cursorCost l ∧
      CursorRuntime l p p.left.length n j t ∧ CursorFrame l s.val t.val := by
  obtain ⟨first,a,ea,hfirst,ha,hba,fa⟩ := h.test input tape s (Nat.zero_le _)
  let invariant (q : ℕ×ℕ×ℕ) (u : Store) : Prop :=
    CursorRuntime l p q.1 q.2.1 q.2.2 u ∧ p.Cursor q.1 q.2.1 q.2.2 ∧
      (u.val.registers 2=true ↔ q.2.1<n) ∧ CursorFrame l s.val u.val
  let measure (q : ℕ×ℕ×ℕ) : ℕ := 2*n-(q.2.1+q.2.2)
  have start : invariant (0,0,0) a := ⟨ha,p.initial,hba,fa⟩
  have step : ∀q u, invariant q u → u.val.registers 2=true →
      ∃cost q' t, Executes input tape cursorBodyCode cost u t ∧ invariant q' t ∧
        measure q'<measure q ∧ cost≤6*operationCap l+2 := by
    rintro ⟨d,i,j⟩ u ⟨hu,hc,hbool,hframe⟩ hb
    change CursorRuntime l p d i j u at hu
    change p.Cursor d i j at hc
    change (u.val.registers 2=true ↔ i<n) at hbool
    have hi := hbool.mp hb
    obtain ⟨cost,t,d',i',j',he,hcost,ht,hnext,hgrow,hb',hf⟩ := cursor_body input tape u hu hc hi
    refine ⟨cost,(d',i',j'),t,he,⟨ht,hnext,hb',hframe.trans hf⟩,?_,hcost⟩
    change 2*n-(i'+j')<2*n-(i+j)
    have hleft := hnext.left_le
    have hright := hnext.right_le
    change i'≤n at hleft
    change j'≤n at hright
    omega
  obtain ⟨rest,⟨d,i,j⟩,t,et,ht,hstop,hrest⟩ :=
    loop_indexed_measure_bound input tape 2 cursorBodyCode invariant measure (6*operationCap l+2)
      step (0,0,0) a start
  rcases ht with ⟨hr,hc,hbool,hframe⟩
  change CursorRuntime l p d i j t at hr
  change p.Cursor d i j at hc
  change (t.val.registers 2=true ↔ i<n) at hbool
  have hi : i=n := by
    have hn : ¬i<n := by
      intro hh
      have := hbool.mpr hh
      rw [hstop] at this
      contradiction
    have := hc.left_le
    omega
  have hd := CompletionPlan.finished hc hi
  refine ⟨first+rest,t,j,ea.seq et,?_,?_,hframe⟩
  · change rest≤1+(2*n-(0+0))*(6*operationCap l+2+1) at hrest
    simp only [Nat.add_zero,Nat.sub_zero] at hrest
    unfold cursorCost
    nlinarith only [hfirst,hrest]
  · simpa only [hd,hi] using hr

theorem cursor_compiled_run {n : ℕ} (l : Layout n) (p : CompletionPlan n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : CursorRuntime l p 0 0 0 s) :
    ∃t j, (runPriced (cursorCode.compile.next input tape) (cursorCost l+1) s.val).finished=
      some (t.place cursorCode.size) ∧
      (runPriced (cursorCode.compile.next input tape) (cursorCost l+1) s.val).instructions≤cursorCost l ∧
      CursorRuntime l p p.left.length n j t ∧ CursorFrame l s.val t.val := by
  obtain ⟨cost,t,j,he,hc,ht,hf⟩ := cursor_executes l p input tape s h
  have hr := he.compiled_run (cursorCost l+1) (by omega)
  exact ⟨t,j,hr.1,hr.2.symm ▸ hc,ht,hf⟩

#print axioms cursor_executes
#print axioms cursor_compiled_run

end Maxwell.Cost.RoutingPorts.Complete
