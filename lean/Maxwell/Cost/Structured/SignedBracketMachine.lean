import Maxwell.Cost.Structured.SignedBracketValues

/-! Executed midpoint and overlapping bracket update. The branch reads the
actual machine register; all copies, arithmetic and old-word clearing are charged. -/
namespace Maxwell.Cost.Structured.SignedBracket
open NatAssign
set_option maxHeartbeats 2000000

def midpointCode (base : ℕ) : Code := NatAssign.code (midpointPlan base)
def stepCode (base register : ℕ) : Code :=
  .branch register (NatAssign.code (stepPlan base true)) (NatAssign.code (stepPlan base false))
def midpointCost (B : ℕ) : ℕ := 3000*8^7*(B+2)^2
def stepCost (B : ℕ) : ℕ := 3000*8^15*(B+2)^2+1

theorem midpoint_executes (b B : ℕ) (hb : 4≤b) (hB : 7≤B) (v : ℕ→ℕ)
    (width : ∀i∈ids b,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : Bank (ids b) v s.val) (scratch : Scratch s.val) :
    ∃steps t,Executes input tape (midpointCode b) steps s t ∧ steps≤midpointCost B ∧
      Bank (ids b) (values (midpointPlan b) v) t.val ∧ Scratch t.val ∧
      (∀i∈ids b,(values (midpointPlan b) v i).bits.length≤B+7) ∧
      BinaryPrecision.Frame ({0,1,2,3}∪ids b) s.val t.val := by
  obtain ⟨c,t,e,charge,stored,blank,frame⟩:=NatAssign.executes (ids b) (ids_lower b hb)
    (midpointPlan b) (midpoint_valid b) v input tape s bank scratch
  have bound:=price_bound (ids b) (midpointPlan b) (midpoint_valid b) v B width
    (fun a ha=>(midpoint_literals b a ha).trans hB)
  exact ⟨c,t,e,charge.trans bound,stored,blank,midpoint_width b B v width,
    frame.mono (midpoint_changes b)⟩

theorem step_executes (b register B : ℕ) (hb : 4≤b) (hB : 7≤B)
    (negative : Bool) (v : ℕ→ℕ) (width : ∀i∈ids b,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : Bank (ids b) v s.val) (scratch : Scratch s.val)
    (decision : s.val.registers register=negative) :
    ∃steps t,Executes input tape (stepCode b register) steps s t ∧ steps≤stepCost B ∧
      Bank (ids b) (values (stepPlan b negative) v) t.val ∧ Scratch t.val ∧
      (∀i∈ids b,(values (stepPlan b negative) v i).bits.length≤B+7) ∧
      BinaryPrecision.Frame ({0,1,2,3}∪ids b) s.val t.val := by
  obtain ⟨c,t,e,charge,stored,blank,frame⟩:=NatAssign.executes (ids b) (ids_lower b hb)
    (stepPlan b negative) (step_valid b negative) v input tape s bank scratch
  have bound:=price_bound (ids b) (stepPlan b negative) (step_valid b negative) v B width
    (fun a ha=>(step_literals b negative a ha).trans hB)
  have length : (stepPlan b negative).length=15 := by cases negative <;> rfl
  rw [length] at bound
  refine ⟨1+c,t,?_,by unfold stepCost;omega,stored,blank,step_width b B negative v width,
    frame.mono (step_changes b negative)⟩
  cases negative
  · exact Executes.no decision e
  · exact Executes.yes decision e

#print axioms midpoint_executes
#print axioms step_executes
end Maxwell.Cost.Structured.SignedBracket
