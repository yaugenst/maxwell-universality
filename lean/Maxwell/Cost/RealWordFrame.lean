import Maxwell.Cost.RealLink

namespace Maxwell.Cost

/-- A decidable property of the fixed code, used to retain caller real
registers across serializers which otherwise only write index memory. -/
def RAMInstruction.writesWordsBelow (bound : ℕ) : RAMInstruction → Bool
  | .literal dst _ | .copy dst _ | .add dst _ _ | .multiply dst _ _ | .divide dst _ _
  | .input dst _ | .load dst _ | .randomBit dst => decide (dst < bound)
  | .store _ _ => false
  | _ => true

def Machine.writesWordsBelow (M : Machine) (bound : ℕ) : Bool :=
  M.code.all (RAMInstruction.writesWordsBelow bound)

theorem Machine.next_high_word (M : Machine) (bound : ℕ)
    (hM : M.writesWordsBelow bound = true) (input : RAMInput) (tape : ℕ → Bool)
    {s t : RAMState} (h : M.next input tape s = some t) (i : ℕ) (hi : bound ≤ i) :
    t.words i = s.words i := by
  cases hc : M.code[s.pc]? with
  | none => simp [Machine.next, hc] at h
  | some instruction =>
    have hm : instruction ∈ M.code := List.mem_of_getElem? hc
    have hs := List.all_eq_true.mp hM instruction hm
    cases instruction <;>
      simp only [Machine.next, hc, Option.some.injEq, reduceCtorEq] at h <;>
      simp only [RAMInstruction.writesWordsBelow, Bool.false_eq_true, decide_eq_true_eq] at hs
    all_goals subst t
    all_goals simp only [RAMState.setWord, RAMState.setIndex]
    all_goals rw [Function.update_of_ne (by omega)]

theorem Steps.high_word {M : Machine} {bound cost : ℕ} {input : RAMInput} {tape : ℕ → Bool}
    {s t : RAMState} (h : Steps (M.next input tape) cost s t)
    (hM : M.writesWordsBelow bound = true) (i : ℕ) (hi : bound ≤ i) :
    t.words i = s.words i := by
  induction h with
  | refl _ => rfl
  | step h _ ih => exact ih.trans (M.next_high_word bound hM input tape h i hi)

theorem Terminates.high_word {M : Machine} {bound cost : ℕ} {input : RAMInput} {tape : ℕ → Bool}
    {s t : RAMState} (h : Terminates (M.next input tape) cost s t)
    (hM : M.writesWordsBelow bound = true) (i : ℕ) (hi : bound ≤ i) :
    t.words i = s.words i := h.toSteps.high_word hM i hi

end Maxwell.Cost
