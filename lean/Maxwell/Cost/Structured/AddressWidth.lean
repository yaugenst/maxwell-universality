import Maxwell.Cost.Structured.Determinism
import Maxwell.Cost.VisitedExecution.Composition

namespace Maxwell.Cost.Structured

/-- An existing charged structured execution together with a bound at every
actual instruction boundary, valid in any static compiled placement. -/
structure Visited (width : ℕ) (input : List Bool) (tape : ℕ→Bool)
    (code : Code) (cost : ℕ) (s t : Store) : Prop where
  execution : Executes input tape code cost s t
  placed : ∀ (machine : BitRAM) (base exitPC : ℕ), Placed machine code base exitPC →
    VisitedPriced (machine.next input tape) (Address.Within width) cost
      (s.place base) (t.place exitPC)

namespace Visited
variable {W : ℕ} {input : List Bool} {tape : ℕ→Bool}
  {code : Code} {cost : ℕ} {s t : Store}

theorem compiled (h : Visited W input tape code cost s t) :
    VisitedPriced (code.compile.next input tape) (Address.Within W) cost
      s.val (t.place code.size) := by
  simpa using h.placed code.compile 0 code.size code.compile_placed

theorem start (h : Visited W input tape code cost s t) : Address.Within W s.val :=
  h.compiled.start

theorem finish (h : Visited W input tape code cost s t) : Address.Within W t.val :=
  h.compiled.finish

theorem prefix_bound (h : Visited W input tape code cost s t) (n : ℕ) (u : BitRAMState)
    (hu : PricedSteps (code.compile.next input tape) n s.val u) : Address.Within W u :=
  h.compiled.prefix_halt (by simp [BitRAM.next,Store.place,code.compile_halt]) hu

theorem mono {V : ℕ} (h : Visited W input tape code cost s t) (hle : W≤V) :
    Visited V input tape code cost s t :=
  ⟨h.execution, fun M base exitPC hp => (h.placed M base exitPC hp).mono (fun _ hh => hh.trans hle)⟩

theorem of_execution {otherCost : ℕ} {u : Store}
    (h : Visited W input tape code cost s t)
    (run : Executes input tape code otherCost s u) :
    Visited W input tape code otherCost s u := by
  rcases h.execution.deterministic run with ⟨rfl,rfl⟩
  exact h

theorem skip (s : Store) (hs : Address.Within W s.val) :
    Visited W input tape .skip 1 s s := by
  refine ⟨.skip s,?_⟩
  intro M base exitPC hp
  apply VisitedPriced.step (extra:=0)
    (rest := .refl (s := s.place exitPC) (show Address.Within W _ from hs))
  · exact hs
  · simp [BitRAM.next,Store.place,hp.skip]

theorem call (body : BitRAM) (s : Store) (t : BitRAMState) (cost : ℕ)
    (h : VisitedPriced (body.next input tape) (Address.Within W) cost s.val t)
    (halt : body.code[t.pc]?=some .halt) :
    Visited W input tape (.call body) (cost+1) s (Store.ofState t) := by
  refine ⟨.call body s t cost h.steps halt,?_⟩
  intro M base exitPC hp
  simpa [BitRAMState.relocate,Store.place,Store.ofState,s.property] using
    hp.call.visited_call input tape h halt

theorem seq {first second : Code} {a b : ℕ} {s t u : Store}
    (h : Visited W input tape first a s t) (k : Visited W input tape second b t u) :
    Visited W input tape (.seq first second) (a+b) s u :=
  ⟨h.execution.seq k.execution, fun M base exitPC hp =>
    (h.placed M base _ hp.seq_first).trans (k.placed M _ exitPC hp.seq_second)⟩

theorem yes {register : ℕ} {yes no : Code} {cost : ℕ} {s t : Store}
    (test : s.val.registers register=true) (h : Visited W input tape yes cost s t) :
    Visited W input tape (.branch register yes no) (1+cost) s t := by
  refine ⟨.yes test h.execution,?_⟩
  intro M base exitPC hp
  have hb : VisitedPriced (M.next input tape) (Address.Within W) 1
      (s.place base) (s.place (base+1)) := by
    apply VisitedPriced.step (extra:=0)
      (rest := .refl (s:=s.place (base+1)) (show Address.Within W _ from h.start))
    · exact h.start
    · simp [BitRAM.next,Store.place,hp.branch_head,test]
  exact hb.trans (h.placed M _ exitPC hp.branch_yes)

theorem no {register : ℕ} {yes no : Code} {cost : ℕ} {s t : Store}
    (test : s.val.registers register=false) (h : Visited W input tape no cost s t) :
    Visited W input tape (.branch register yes no) (1+cost) s t := by
  refine ⟨.no test h.execution,?_⟩
  intro M base exitPC hp
  have hb : VisitedPriced (M.next input tape) (Address.Within W) 1
      (s.place base) (s.place (base+1+yes.size)) := by
    apply VisitedPriced.step (extra:=0)
      (rest := .refl (s:=s.place (base+1+yes.size)) (show Address.Within W _ from h.start))
    · exact h.start
    · simp [BitRAM.next,Store.place,hp.branch_head,test]
  exact hb.trans (h.placed M _ exitPC hp.branch_no)

theorem done {register : ℕ} {body : Code} {s : Store}
    (test : s.val.registers register=false) (hs : Address.Within W s.val) :
    Visited W input tape (.loop register body) 1 s s := by
  refine ⟨.done test,?_⟩
  intro M base exitPC hp
  apply VisitedPriced.step (extra:=0)
    (rest := .refl (s:=s.place exitPC) (show Address.Within W _ from hs))
  · exact hs
  · simp [BitRAM.next,Store.place,hp.loop_head,test]

theorem more {register : ℕ} {body : Code} {a b : ℕ} {s t u : Store}
    (test : s.val.registers register=true) (h : Visited W input tape body a s t)
    (k : Visited W input tape (.loop register body) b t u) :
    Visited W input tape (.loop register body) (1+a+b) s u := by
  refine ⟨.more test h.execution k.execution,?_⟩
  intro M base exitPC hp
  have hb : VisitedPriced (M.next input tape) (Address.Within W) 1
      (s.place base) (s.place (base+1)) := by
    apply VisitedPriced.step (extra:=0)
      (rest := .refl (s:=s.place (base+1)) (show Address.Within W _ from h.start))
    · exact h.start
    · simp [BitRAM.next,Store.place,hp.loop_head,test]
  exact (hb.trans (h.placed M _ base hp.loop_body)).trans (k.placed M base exitPC hp)
end Visited

/-- Arithmetic and tape-only code cannot grow the explicit address register. -/
def Code.noAddressPush : Code→Bool
  | .skip => true
  | .call body => body.noAddressPush
  | .seq first second => first.noAddressPush && second.noAddressPush
  | .branch _ yes no => yes.noAddressPush && no.noAddressPush
  | .loop _ body => body.noAddressPush

theorem Executes.visited_noAddressPush {input : List Bool} {tape : ℕ→Bool}
    {code : Code} {cost W : ℕ} {s t : Store} (run : Executes input tape code cost s t)
    (hp : code.noAddressPush=true) (hs : Address.Within W s.val) :
    Visited W input tape code cost s t := by
  induction run with
  | skip s => exact .skip s hs
  | call body s t cost steps halt => exact .call body s t cost (steps.visited_noAddressPush hp hs) halt
  | seq _ _ ih1 ih2 =>
    simp only [Code.noAddressPush,Bool.and_eq_true] at hp
    have h := ih1 hp.1 hs
    exact h.seq (ih2 hp.2 h.finish)
  | yes test _ ih =>
    simp only [Code.noAddressPush,Bool.and_eq_true] at hp
    exact .yes test (ih hp.1 hs)
  | no test _ ih =>
    simp only [Code.noAddressPush,Bool.and_eq_true] at hp
    exact .no test (ih hp.2 hs)
  | done test => exact .done test hs
  | more test _ _ ih1 ih2 =>
    have h := ih1 hp hs
    exact .more test h (ih2 hp h.finish)

end Maxwell.Cost.Structured
