import Maxwell.Continuum.OutputCaptureCode

/-! Instruction-level, fully charged simulation of retained output. -/
namespace Maxwell.Continuum.OutputCapture
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2000000

theorem step (archive : ℕ) (body : BitRAM)
    (hp : body.code.all (avoids archive)=true)
    (input : List Bool) (tape : ℕ→Bool) (s t : BitRAMState) (extra : ℕ)
    (hn : body.next input tape s=some ⟨t,extra⟩)
    (output accumulated : List Bool) :
    ∃ cost bits, cost≤2*(extra+1) ∧ bits.length≤extra+1 ∧
      t.output=bits.reverse++s.output ∧
      PricedSteps ((program archive body).next input tape) cost
        (state archive output accumulated s)
        (state archive output (accumulated++bits) t) := by
  cases hi : body.code[s.pc]? with
  | none => simp [BitRAM.next,hi] at hn
  | some instruction =>
    have ha := List.all_eq_true.mp hp instruction (List.mem_of_getElem? hi)
    have hfirst := lookup_first archive body s.pc instruction hi
    have hsecond := lookup_second archive body s.pc instruction hi
    cases instruction <;>
      simp only [BitRAM.next,hi,Option.some.injEq,PricedStep.mk.injEq] at hn <;>
      try contradiction
    all_goals rcases hn with ⟨rfl,he⟩
    all_goals simp only [avoids,decide_eq_true_eq] at ha
    case output register =>
      refine ⟨2,[s.registers register],by omega,by simp,by simp,?_⟩
      apply executeInstructions_sound (instructions:=2)
      simp [executeInstructions,BitRAM.next,state,hfirst,hsecond,first,second,
        BitRAMState.setTape,Nat.mul_add,Nat.add_assoc]
      exact congrArg (Function.update s.tapes archive)
        (BitTape.append_write accumulated (s.registers register))
    case branch register yes no =>
      refine ⟨1,[],by omega,by simp,by simp,?_⟩
      apply executeInstructions_sound (instructions:=1)
      cases h : s.registers register <;>
        simp [executeInstructions,BitRAM.next,state,hfirst,first,h]
    case jump target =>
      refine ⟨1,[],by omega,by simp,by simp,?_⟩
      apply executeInstructions_sound (instructions:=1)
      simp [executeInstructions,BitRAM.next,state,hfirst,first]
    all_goals
      refine ⟨extra+2,[],by omega,by simp,by rfl,?_⟩
      apply executeInstructions_sound (instructions:=2)
      simp [executeInstructions,BitRAM.next,state,hfirst,hsecond,first,second,
        BitRAMState.setTape,BitRAMState.setRegister,ha,Nat.mul_add,←he]
      try exact Function.update_comm (Ne.symm ha) _ _ _

end Maxwell.Continuum.OutputCapture
