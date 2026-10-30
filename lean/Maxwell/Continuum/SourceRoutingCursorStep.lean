import Maxwell.Continuum.SourceRoutingCursorMachine

/-! The literal branching step of the two-pointer completion algorithm.
Every branch is selected by an actual sentinel comparison. -/

namespace Maxwell.Cost.RoutingPorts.Complete
open Structured
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def cursorStepCode : Code :=
  .seq (probeCode 730 716)
    (.branch 2 (PhysicalEmit.incrementCode 730)
      (.seq (probeCode 731 717)
        (.branch 2 (PhysicalEmit.incrementCode 731)
          (.seq pairCode (.seq (PhysicalEmit.incrementCode 730) (PhysicalEmit.incrementCode 731))))))

theorem cursor_step {n : ℕ} {l : Layout n} {p : CompletionPlan n} {d i j : ℕ}
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : CursorRuntime l p d i j s) (hc : p.Cursor d i j) (hi : i<n) :
    ∃cost t d' i' j', Executes input tape cursorStepCode cost s t ∧
      cost≤5*operationCap l+2 ∧ CursorRuntime l p d' i' j' t ∧
      p.Cursor d' i' j' ∧ i+j < i'+j' ∧ CursorFrame l s.val t.val := by
  obtain ⟨ca,a,ea,hca,ha,hba,fa⟩ := h.probe_left input tape s hi
  cases htesta : a.val.registers 2 with
  | true =>
    obtain ⟨cb,t,eb,hcb,ht,fb⟩ := ha.increment_left input tape a hi.le
    exact ⟨ca+(1+cb),t,d,i+1,j,ea.seq (Executes.yes htesta eb),by omega,
      ht,CompletionPlan.advance_left hc hi (hba.mp htesta),by omega,fa.trans fb⟩
  | false =>
    have hleft : (p.forward d).get ⟨i,hi⟩=n := by
      have hle := p.forward_le d ⟨i,hi⟩
      have hn : ¬(p.forward d).get ⟨i,hi⟩<n := by
        intro hh
        have := hba.mpr hh
        rw [htesta] at this
        contradiction
      omega
    have hj := CompletionPlan.right_available hc hi hleft
    obtain ⟨cb,b,eb,hcb,hb,hbb,fb⟩ := ha.probe_right input tape a hj
    cases htestb : b.val.registers 2 with
    | true =>
      obtain ⟨cc,t,ec,hcc,ht,fc⟩ := hb.increment_right input tape b hj.le
      exact ⟨ca+(1+(cb+(1+cc))),t,d,i,j+1,
        ea.seq (Executes.no htesta (eb.seq (Executes.yes htestb ec))),by omega,
        ht,CompletionPlan.advance_right hc hj (hbb.mp htestb),by omega,fa.trans (fb.trans fc)⟩
    | false =>
      have hright : (p.backward d).get ⟨j,hj⟩=n := by
        have hle := p.backward_le d ⟨j,hj⟩
        have hn : ¬(p.backward d).get ⟨j,hj⟩<n := by
          intro hh
          have := hbb.mpr hh
          rw [htestb] at this
          contradiction
        omega
      obtain ⟨hd,hpair,hnext⟩ := CompletionPlan.next_pair hc hi hj hleft hright
      obtain ⟨cc,c,ec,hcc,hc',fc⟩ := hb.write_pair input tape b hi hj hd hpair
      obtain ⟨ce,e,ee,hce,he,fe⟩ := hc'.increment_left input tape c hi.le
      obtain ⟨ct,t,et,hct,ht,ft⟩ := he.increment_right input tape e hj.le
      exact ⟨ca+(1+(cb+(1+(cc+(ce+ct))))),t,d+1,i+1,j+1,
        ea.seq (Executes.no htesta (eb.seq (Executes.no htestb (ec.seq (ee.seq et))))),
        by omega,ht,hnext,by omega,fa.trans (fb.trans (fc.trans (fe.trans ft)))⟩

def cursorBodyCode : Code := .seq cursorStepCode (cursorTestCode 730)

theorem cursor_body {n : ℕ} {l : Layout n} {p : CompletionPlan n} {d i j : ℕ}
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : CursorRuntime l p d i j s) (hc : p.Cursor d i j) (hi : i<n) :
    ∃cost t d' i' j', Executes input tape cursorBodyCode cost s t ∧
      cost≤6*operationCap l+2 ∧ CursorRuntime l p d' i' j' t ∧
      p.Cursor d' i' j' ∧ i+j < i'+j' ∧ (t.val.registers 2=true ↔ i'<n) ∧
      CursorFrame l s.val t.val := by
  obtain ⟨ca,a,d',i',j',ea,hca,ha,hnext,hgrow,fa⟩ := cursor_step input tape s h hc hi
  obtain ⟨cb,t,eb,hcb,ht,hb,fb⟩ := ha.test input tape a hnext.left_le
  exact ⟨ca+cb,t,d',i',j',ea.seq eb,by omega,ht,hnext,hgrow,hb,fa.trans fb⟩

#print axioms cursor_step
#print axioms cursor_body

end Maxwell.Cost.RoutingPorts.Complete
