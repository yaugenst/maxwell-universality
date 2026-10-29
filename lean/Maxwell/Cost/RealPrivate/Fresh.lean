import Maxwell.Cost.RealSimulation.VisitedSteps

namespace Maxwell.Cost.RealPrivate

/-- Literal register destinations of fixed caller code lie below the chosen
fresh origin. Dynamic destinations are bounded by the actual word trace. -/
def StaticDestinationBound (origin : ℕ) : RAMInstruction → Prop
  | .literal dst _ | .copy dst _ | .add dst _ _ | .multiply dst _ _ | .divide dst _ _ |
      .input dst _ | .load dst _ | .randomBit dst | .inputIndex dst _ | .loadIndex dst _ |
      .indexLiteral dst _ | .indexCopy dst _ | .indexAdd dst _ _ | .indexSubtract dst _ _ =>
      dst < origin
  | _ => True

def CodeDestinationBound (origin : ℕ) (M : Machine) : Prop :=
  ∀ op ∈ M.code, StaticDestinationBound origin op

theorem next_high_cells {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {origin : ℕ} (code : CodeDestinationBound origin M)
    {s t : RAMState} (addresses : ∀ r, s.indices r < origin)
    (step : M.next input tape s = some t) (j : ℕ) (hj : origin ≤ j) :
    t.words j = s.words j ∧ t.indices j = s.indices j := by
  cases hc : M.code[s.pc]? with
  | none => simp [Machine.next, hc] at step
  | some op =>
    have hd := code op (List.mem_of_getElem? hc)
    cases op <;> simp only [StaticDestinationBound] at hd
    all_goals simp only [Machine.next, hc, Option.some.injEq, reduceCtorEq] at step
    all_goals subst t
    all_goals simp only [RAMState.setWord, RAMState.setIndex]
    all_goals constructor
    all_goals try trivial
    all_goals apply Function.update_of_ne
    all_goals first | omega | exact ne_of_gt ((addresses _).trans_le hj)

theorem visited_high_cells {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {origin width n : ℕ} {s t : RAMState}
    (trace : RealSimulation.VisitedSteps (M.next input tape)
      (RealSimulation.IndexWordWidth width) n s t)
    (code : CodeDestinationBound origin M) (large : 2 ^ width ≤ origin)
    (j : ℕ) (hj : origin ≤ j) : t.words j = s.words j ∧ t.indices j = s.indices j := by
  induction trace with
  | refl => exact ⟨rfl, rfl⟩
  | step hs hn _ ih =>
    have hf := next_high_cells code (fun r =>
      (Nat.size_le.mp (hs r)).trans_le large) hn j hj
    exact ⟨ih.1.trans hf.1, ih.2.trans hf.2⟩

/-- Freshness follows from an actual bounded caller trace starting at the
ordinary all-zero RAM state; no fresh-memory oracle is assumed. -/
theorem fresh_of_initial_trace {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {origin width n : ℕ} {t : RAMState}
    (trace : RealSimulation.VisitedSteps (M.next input tape)
      (RealSimulation.IndexWordWidth width) n RAMState.initial t)
    (code : CodeDestinationBound origin M) (large : 2 ^ width ≤ origin)
    (j : ℕ) (hj : origin ≤ j) : t.words j = 0 ∧ t.indices j = 0 :=
  visited_high_cells trace code large j hj

end Maxwell.Cost.RealPrivate
