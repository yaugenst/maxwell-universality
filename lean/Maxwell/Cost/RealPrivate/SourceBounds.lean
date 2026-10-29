import Maxwell.Cost.Execution

namespace Maxwell.Cost.RealPrivate.SourceBounds

/-- One actual source instruction appends at most one value to either
output channel and consumes at most one random bit. -/
theorem next_bounds {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {s t : RAMState} (h : M.next input tape s = some t) :
    t.output.length ≤ s.output.length+1 ∧
      t.indexOutput.length ≤ s.indexOutput.length+1 ∧
      s.randomCursor ≤ t.randomCursor ∧ t.randomCursor ≤ s.randomCursor+1 := by
  cases hc : M.code[s.pc]? with
  | none => simp [Machine.next, hc] at h
  | some op =>
    cases op <;> simp only [Machine.next, hc, Option.some.injEq, reduceCtorEq] at h
    all_goals subst t
    all_goals simp [RAMState.setWord, RAMState.setIndex]

/-- The bounds count concrete source transitions, including every random
draw and every write to an output channel. -/
theorem steps_bounds {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {n : ℕ} {s t : RAMState} (h : Steps (M.next input tape) n s t) :
    t.output.length ≤ s.output.length+n ∧
      t.indexOutput.length ≤ s.indexOutput.length+n ∧
      s.randomCursor ≤ t.randomCursor ∧ t.randomCursor ≤ s.randomCursor+n := by
  induction h with
  | refl => simp
  | step hn _ ih =>
    have hb := next_bounds hn
    omega

/-- Any prefix within the source fuel budget fits the two finite output
buffers. The incoming random cursor is retained explicitly. -/
theorem initial_prefix_bounds {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {n fuel randomBase : ℕ} {t : RAMState}
    (h : Steps (M.next input tape) n {RAMState.initial with randomCursor := randomBase} t)
    (hn : n ≤ fuel) :
    t.output.length ≤ fuel ∧ t.indexOutput.length ≤ fuel ∧
      randomBase ≤ t.randomCursor ∧ t.randomCursor ≤ randomBase+fuel := by
  have hb := steps_bounds h
  simp only [RAMState.initial, List.length_nil, Nat.zero_add] at hb
  omega

private theorem terminates_steps {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {n : ℕ} {s t : RAMState} (h : Terminates (M.next input tape) n s t) :
    Steps (M.next input tape) n s t := by
  induction h with
  | halt => exact Steps.refl _
  | step he _ ih => exact Steps.step he ih

theorem capped_bounds {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {fuel : ℕ} {s t : RAMState}
    (h : (runCapped (M.next input tape) fuel s).finished = some t) :
    t.output.length ≤ s.output.length+fuel ∧
      t.indexOutput.length ≤ s.indexOutput.length+fuel ∧
      s.randomCursor ≤ t.randomCursor ∧ t.randomCursor ≤ s.randomCursor+fuel := by
  have ht := runCapped_sound (M.next input tape) fuel h
  have hs := terminates_steps ht
  have hb := steps_bounds hs
  have hc := runCapped_le (M.next input tape) fuel s
  omega

theorem initial_capped_bounds {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {fuel randomBase : ℕ} {t : RAMState}
    (h : (runCapped (M.next input tape) fuel
      {RAMState.initial with randomCursor := randomBase}).finished = some t) :
    t.output.length ≤ fuel ∧ t.indexOutput.length ≤ fuel ∧
      randomBase ≤ t.randomCursor ∧ t.randomCursor ≤ randomBase+fuel := by
  simpa only [RAMState.initial, List.length_nil, Nat.zero_add] using capped_bounds h

end Maxwell.Cost.RealPrivate.SourceBounds
