import Maxwell.Cost.Structured.NaturalWordTest

/-! A fixed loop controlled by a canonical runtime natural word. Its body
must execute the decrement itself; the guard only reads whether the word is
empty. This supports bodies that retain canonical counters between calls. -/
namespace Maxwell.Cost.Structured.NaturalCountdown

def code (countTape flag : ℕ) (body : Code) : Code :=
  .seq (NaturalWordTest.code countTape flag)
    (.loop flag (.seq body (NaturalWordTest.code countTape flag)))

theorem executes (countTape flag : ℕ) (body : Code) (input : List Bool) (tape : ℕ→Bool)
    (invariant : ℕ→Store→Prop)
    (stable : ∀n s t,BinaryPrecision.Frame ∅ s.val t.val→invariant n s→invariant n t)
    (bodyCorrect : ∀n s,invariant (n+1) s→RationalAccumulator.Word s.val countTape (n+1)→
      ∃cost t,Executes input tape body cost s t ∧ invariant n t ∧ RationalAccumulator.Word t.val countTape n)
    (n : ℕ) (s : Store) (state : invariant n s) (word : RationalAccumulator.Word s.val countTape n) :
    ∃cost t,Executes input tape (code countTape flag body) cost s t ∧
      invariant 0 t ∧ RationalAccumulator.Word t.val countTape 0 ∧ t.val.registers flag=false := by
  induction n generalizing s with
  | zero =>
    obtain ⟨t,execution,flagValue,frame⟩:=NaturalWordTest.executes countTape flag 0 input tape s word
    have stopped : t.val.registers flag=false := by simpa only [Nat.lt_irrefl,decide_false] using flagValue
    exact ⟨4,t,execution.seq (.done stopped),stable 0 s t frame state,
      RationalAccumulator.word_of_eq (frame.tapes _ (by simp)) word,stopped⟩
  | succ n ih =>
    obtain ⟨u,test,flagValue,frame⟩:=NaturalWordTest.executes countTape flag (n+1) input tape s word
    have continued : u.val.registers flag=true := by simpa only [Nat.zero_lt_succ,decide_true] using flagValue
    obtain ⟨c0,v,iteration,ready,remaining⟩:=bodyCorrect n u (stable (n+1) s u frame state)
      (RationalAccumulator.word_of_eq (frame.tapes _ (by simp)) word)
    obtain ⟨c1,t,rest,finished,zero,stopped⟩:=ih v ready remaining
    change Executes input tape (.seq (NaturalWordTest.code countTape flag)
      (.loop flag (.seq body (NaturalWordTest.code countTape flag)))) c1 v t at rest
    cases rest with
    | seq nextTest nextLoop =>
      exact ⟨_,t,test.seq (.more continued (iteration.seq nextTest) nextLoop),finished,zero,stopped⟩

#print axioms executes
end Maxwell.Cost.Structured.NaturalCountdown
