import Maxwell.Cost.RealSimulation.ControlCorrectness
import Maxwell.Cost.RealSimulation.VisitedLink

namespace Maxwell.Cost.RealSimulation.Control
open IndexWidth

/-- Two terminating executions of the same finite program on the same
stored input have identical charged costs and final stores. -/
theorem Executes.deterministic {input : RAMInput} {randomTape : ℕ → Bool}
    {code : Code} {a b : ℕ} {s t u : Store}
    (first : Executes input randomTape code a s t)
    (second : Executes input randomTape code b s u) : a = b ∧ t = u := by
  have ht := first.compiled_run (a+b+1) (by omega)
  have hu := second.compiled_run (a+b+1) (by omega)
  refine ⟨ht.2.symm.trans hu.2, ?_⟩
  have hplace : t.place code.size = u.place code.size :=
    Option.some.inj (ht.1.symm.trans hu.1)
  have hstore := congrArg Store.ofState hplace
  have reset (v : Store) : Store.ofState (v.place code.size) = v := by
    apply Subtype.ext
    change { v.val with pc := 0 } = v.val
    cases v with
    | mk val hv =>
      cases val
      cases hv
      rfl
  simpa only [reset] using hstore


/-- Structured execution with a common bound at every macro boundary.
An atom is an actual, bounded-length execution of finite compiled code. -/
inductive BoundedExecutes (B C : ℕ) (input : RAMInput) (randomTape : ℕ → Bool) :
    Code → ℕ → Store → Store → Prop where
  | atom {code : Code} {cost : ℕ} {s t : Store}
      (actual : Executes input randomTape code cost s t) (cost_le : cost ≤ C)
      (start_bound : IndexBound B s.val) (end_bound : IndexBound B t.val) :
      BoundedExecutes B C input randomTape code cost s t
  | tracedCall {body : Machine} {cost : ℕ} {s : Store} {t : RAMState}
      (trace : VisitedSteps (body.next input randomTape) (IndexBound (2^C*B)) cost s.val t)
      (halt : body.code[t.pc]?=some .halt)
      (start_bound : IndexBound B s.val) (end_bound : IndexBound B t) :
      BoundedExecutes B C input randomTape (.call body) (cost+1) s (Store.ofState t)
  | skip {s : Store} (bound : IndexBound B s.val) :
      BoundedExecutes B C input randomTape .skip 1 s s
  | seq {first second : Code} {a b : ℕ} {s t u : Store}
      (firstRun : BoundedExecutes B C input randomTape first a s t)
      (secondRun : BoundedExecutes B C input randomTape second b t u) :
      BoundedExecutes B C input randomTape (.seq first second) (a+b) s u
  | yes {left right : ℕ} {yes no : Code} {cost : ℕ} {s t : Store}
      (test : s.val.indices left ≤ s.val.indices right)
      (body : BoundedExecutes B C input randomTape yes cost s t) :
      BoundedExecutes B C input randomTape (.branch left right yes no) (1+cost) s t
  | no {left right : ℕ} {yes no : Code} {cost : ℕ} {s t : Store}
      (test : ¬s.val.indices left ≤ s.val.indices right)
      (body : BoundedExecutes B C input randomTape no cost s t) :
      BoundedExecutes B C input randomTape (.branch left right yes no) (1+cost) s t
  | done {left right : ℕ} {body : Code} {s : Store}
      (test : ¬s.val.indices left ≤ s.val.indices right) (bound : IndexBound B s.val) :
      BoundedExecutes B C input randomTape (.loop left right body) 1 s s
  | more {left right : ℕ} {body : Code} {a b : ℕ} {s t u : Store}
      (test : s.val.indices left ≤ s.val.indices right)
      (bodyRun : BoundedExecutes B C input randomTape body a s t)
      (rest : BoundedExecutes B C input randomTape (.loop left right body) b t u) :
      BoundedExecutes B C input randomTape (.loop left right body) (1+a+b) s u

theorem BoundedExecutes.executes {B C : ℕ} {input : RAMInput} {randomTape : ℕ → Bool}
    {code : Code} {cost : ℕ} {s t : Store}
    (h : BoundedExecutes B C input randomTape code cost s t) :
    Executes input randomTape code cost s t := by
  induction h with
  | atom actual _ _ _ => exact actual
  | tracedCall trace halt _ _ => exact .call _ _ _ _ trace.steps halt
  | skip => exact .skip _
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | yes test _ ih => exact .yes test ih
  | no test _ ih => exact .no test ih
  | done test _ => exact .done test
  | more test _ _ ih1 ih2 => exact .more test ih1 ih2

theorem BoundedExecutes.start {B C : ℕ} {input : RAMInput} {randomTape : ℕ → Bool}
    {code : Code} {cost : ℕ} {s t : Store}
    (h : BoundedExecutes B C input randomTape code cost s t) : IndexBound B s.val := by
  induction h <;> assumption

theorem BoundedExecutes.finish {B C : ℕ} {input : RAMInput} {randomTape : ℕ → Bool}
    {code : Code} {cost : ℕ} {s t : Store}
    (h : BoundedExecutes B C input randomTape code cost s t) : IndexBound B t.val := by
  induction h <;> assumption

/-- Increasing either common budget preserves the same actual execution. -/
theorem BoundedExecutes.mono {B B' C C' : ℕ} {input : RAMInput} {randomTape : ℕ → Bool}
    {code : Code} {cost : ℕ} {s t : Store}
    (execution : BoundedExecutes B C input randomTape code cost s t)
    (hB : B ≤ B') (hC : C ≤ C') :
    BoundedExecutes B' C' input randomTape code cost s t := by
  induction execution with
  | atom actual cost_le hs ht => exact .atom actual (cost_le.trans hC) (hs.mono hB) (ht.mono hB)
  | tracedCall trace halt hs ht =>
    apply BoundedExecutes.tracedCall (halt := halt) (start_bound := hs.mono hB)
      (end_bound := ht.mono hB)
    exact trace.mono (fun _ hu => hu.mono
      (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hC) hB))
  | skip bound => exact .skip (bound.mono hB)
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | yes test _ ih => exact .yes test ih
  | no test _ ih => exact .no test ih
  | done test bound => exact .done test (bound.mono hB)
  | more test _ _ ih1 ih2 => exact .more test ih1 ih2

private theorem inflate {B C : ℕ} {s : RAMState} (h : IndexBound B s) :
    IndexBound (2^C*B) s := by
  apply h.mono
  have hp : 1 ≤ 2^C := Nat.one_le_pow _ _ (by decide)
  nlinarith

/-- Relocation and arbitrary surrounding code do not affect the macro
boundary argument. The exponent is the maximum atom length, not runtime. -/
theorem BoundedExecutes.placed {B C : ℕ} {input : RAMInput} {randomTape : ℕ → Bool}
    {code : Code} {cost : ℕ} {s t : Store}
    (execution : BoundedExecutes B C input randomTape code cost s t)
    (machine : Machine) (base exitPC : ℕ) (placement : Placed machine code base exitPC)
    (literals : LiteralBound B machine) (inputs : InputBound B input) :
    VisitedSteps (machine.next input randomTape) (IndexBound (2^C*B)) cost
      (s.place base) (t.place exitPC) := by
  induction execution generalizing machine base exitPC with
  | @atom code cost s t actual cost_le hs _ =>
    have hs' : IndexBound B (s.place base) := hs
    have h := visited_index_bound hs' literals inputs le_rfl (actual.placed machine base exitPC placement)
    apply h.mono
    intro u hu
    apply hu.mono
    exact Nat.mul_le_mul_right B (Nat.pow_le_pow_right (by decide) cost_le)
  | @tracedCall body cost s t trace halt _ _ =>
    have h := trace.call placement.call halt
    simpa [RAMState.relocate,Store.place,Store.ofState,s.property] using h
  | @skip s bound =>
    have hs : IndexBound (2^C*B) (s.place base) := inflate bound
    have ht : IndexBound (2^C*B) (s.place exitPC) := inflate bound
    apply VisitedSteps.step hs (rest := .refl ht)
    simp [Machine.next,Store.place,placement.skip]
  | seq firstRun secondRun ih1 ih2 =>
    exact (ih1 machine base _ placement.seq_first literals).trans
      (ih2 machine _ exitPC placement.seq_second literals)
  | @yes left right yes no cost s t test body ih =>
    have hs : IndexBound (2^C*B) (s.place base) := inflate body.start
    have ht := ih machine (base+1) exitPC placement.branch_yes literals
    have hn : machine.next input randomTape (s.place base)=some (s.place (base+1)) := by
      simp [Machine.next,Store.place,placement.branch_head,test]
    simpa only [Nat.add_comm] using VisitedSteps.step hs hn ht
  | @no left right yes no cost s t test body ih =>
    have hs : IndexBound (2^C*B) (s.place base) := inflate body.start
    have ht := ih machine (base+1+yes.size) exitPC placement.branch_no literals
    have hn : machine.next input randomTape (s.place base)=some (s.place (base+1+yes.size)) := by
      simp [Machine.next,Store.place,placement.branch_head,test]
    simpa only [Nat.add_comm] using VisitedSteps.step hs hn ht
  | @done left right body s test bound =>
    have hs : IndexBound (2^C*B) (s.place base) := inflate bound
    have ht : IndexBound (2^C*B) (s.place exitPC) := inflate bound
    apply VisitedSteps.step hs (rest := .refl ht)
    simp [Machine.next,Store.place,placement.loop_head,test]
  | @more left right body a b s t u test bodyRun rest ih1 ih2 =>
    have hs : IndexBound (2^C*B) (s.place base) := inflate bodyRun.start
    have hb := ih1 machine (base+1) base placement.loop_body literals
    have hr := ih2 machine base exitPC placement literals
    have hn : machine.next input randomTape (s.place base)=some (s.place (base+1)) := by
      simp [Machine.next,Store.place,placement.loop_head,test]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using VisitedSteps.step hs hn (hb.trans hr)

theorem BoundedExecutes.compiled {B C : ℕ} {input : RAMInput} {randomTape : ℕ → Bool}
    {code : Code} {cost : ℕ} {s t : Store}
    (execution : BoundedExecutes B C input randomTape code cost s t)
    (literals : LiteralBound B code.compile) (inputs : InputBound B input) :
    VisitedSteps (code.compile.next input randomTape) (IndexBound (2^C*B)) cost
      s.val (t.place code.size) := by
  simpa using execution.placed code.compile 0 code.size code.compile_placed literals inputs

/-- Every actual prefix, including the final state, obeys the same bound. -/
theorem BoundedExecutes.prefix {B C : ℕ} {input : RAMInput} {randomTape : ℕ → Bool}
    {code : Code} {cost : ℕ} {s t : Store}
    (execution : BoundedExecutes B C input randomTape code cost s t)
    (literals : LiteralBound B code.compile) (inputs : InputBound B input)
    {k : ℕ} {u : RAMState} (hk : k ≤ cost)
    (tracePrefix : Steps (code.compile.next input randomTape) k s.val u) : IndexBound (2^C*B) u :=
  (execution.compiled literals inputs).prefix hk tracePrefix

/-- A logarithmic boundary budget gives a logarithmic word budget for the
entire actual trace, with only the fixed macro-length additive overhead. -/
theorem BoundedExecutes.word_width {B C : ℕ} {input : RAMInput} {randomTape : ℕ → Bool}
    {code : Code} {cost : ℕ} {s t : Store}
    (execution : BoundedExecutes B C input randomTape code cost s t)
    (literals : LiteralBound B code.compile) (inputs : InputBound B input) :
    VisitedSteps (code.compile.next input randomTape) (IndexWordWidth (C+B.size)) cost
      s.val (t.place code.size) := by
  apply (execution.compiled literals inputs).mono
  intro u hu j
  apply Nat.size_le.mpr
  have hp : 0<2^C := Nat.pow_pos (by decide)
  have hh := Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self B) hp
  rw [←pow_add] at hh
  exact (hu j).trans_lt hh

end Maxwell.Cost.RealSimulation.Control
