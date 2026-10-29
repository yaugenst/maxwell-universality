import Maxwell.Cost.RealSourceNormalize.Program

namespace Maxwell.Cost.RealSourceNormalize
open RealSimulation.Control
open RealNormalize (normalized scale)
set_option maxRecDepth 20000

/-- Both normalizations are actual passes over disjoint caller arrays.
The matrix and source scales are retained in real registers20 and21. -/
theorem executes (input : RAMInput) (tape : ℕ → Bool) (rb vb d m : ℕ)
    (values rhs : ℕ → ℝ) (s : Store) (hrb : 32 ≤ rb) (hvb : 32 ≤ vb)
    (hsep : rb + m ≤ vb) (hreal : s.val.indices 25 = rb)
    (hd : s.val.indices 52 = d) (hm : s.val.indices 53 = m) (hvbreg : s.val.indices 54 = vb)
    (hv : ∀ j < m, s.val.words (rb + j) = values j)
    (hrhs : ∀ j < d, s.val.words (vb + j) = rhs j) :
    ∃ t : Store, Executes input tape code (22 * m + 22 * d + 44) s t ∧
      (∀ j < m, t.val.words (rb + j) = normalized true m values j) ∧
      (∀ j < d, t.val.words (vb + j) = normalized false d rhs j) ∧
      t.val.words 20 = scale true m values ∧ t.val.words 21 = scale false d rhs ∧
      (∀ i, 4 ≤ i → i ≠ 24 → i ≠ 26 → i ≠ 55 → t.val.indices i = s.val.indices i) ∧
      t.val.output = s.val.output ∧ t.val.indexOutput = s.val.indexOutput ∧
      t.val.randomCursor = s.val.randomCursor := by
  let a := matrixState s
  obtain ⟨r₁, ht₁, hpc₁, _, hscale₁, hvalues₁, hf₁⟩ :=
    RealArrayNormalize.terminates true input tape rb m values a.val hrb a.property
      (by simpa [a, matrixState, Store.ofState, RAMState.setIndex] using hreal)
      (by simp [a, matrixState, Store.ofState, RAMState.setIndex, hm]) hv
  let s₁ := Store.ofState r₁
  have he₁ := Executes.call (RealArrayNormalize.program true) a r₁ (22 * m + 15) ht₁.toSteps
    (by simp [RealArrayNormalize.program, hpc₁])
  have mi (i : ℕ) (hi : 4 ≤ i) (h24 : i ≠ 24) (h26 : i ≠ 26) (h55 : i ≠ 55) :
      r₁.indices i = s.val.indices i := by
    simpa [a, matrixState, Store.ofState, RAMState.setIndex, h26, h55] using hf₁.indices i hi h24
  have m55 : r₁.indices 55 = s.val.indices 25 := by
    simpa [a, matrixState, Store.ofState, RAMState.setIndex] using hf₁.indices 55 (by omega) (by omega)
  let b := sourceState (savedState 20 s₁)
  have bvalues : ∀ j < d, b.val.words (vb + j) = rhs j := by
    intro j hj
    have he := (hf₁.words (vb + j) (by omega) (Or.inr (by omega))).trans (hrhs j hj)
    simpa [b, sourceState, savedState, s₁, Store.ofState, RAMState.setIndex, RAMState.setWord,
      show vb + j ≠ 20 by omega] using he
  obtain ⟨r₂, ht₂, hpc₂, _, hscale₂, hvalues₂, hf₂⟩ :=
    RealArrayNormalize.terminates false input tape vb d rhs b.val hvb b.property
      (by simp [b, sourceState, savedState, s₁, Store.ofState, RAMState.setIndex, RAMState.setWord,
        mi 54 (by omega) (by omega) (by omega) (by omega), hvbreg])
      (by simp [b, sourceState, savedState, s₁, Store.ofState, RAMState.setIndex, RAMState.setWord,
        mi 52 (by omega) (by omega) (by omega) (by omega), hd]) bvalues
  let s₂ := Store.ofState r₂
  have he₂ := Executes.call (RealArrayNormalize.program false) b r₂ (22 * d + 15) ht₂.toSteps
    (by simp [RealArrayNormalize.program, hpc₂])
  let c := savedState 21 s₂
  let t := Store.ofState (c.val.setIndex 25 (c.val.indices 55))
  have scale20 : r₂.words 20 = scale true m values := by
    have he := hf₂.words 20 (by omega) (Or.inl (by omega))
    simpa [b, sourceState, savedState, s₁, Store.ofState, RAMState.setIndex, RAMState.setWord, hscale₁] using he
  refine ⟨t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert (matrix_executes input tape s).seq (he₁.seq ((save_executes input tape 20 s₁).seq
      ((source_executes input tape (savedState 20 s₁)).seq (he₂.seq
        ((save_executes input tape 21 s₂).seq (RealSourceSerialize.copy_executes input tape 25 55 c)))))) using 1 <;> try rfl
    omega
  · intro j hj
    have he := hf₂.words (rb + j) (by omega) (Or.inl (by omega))
    have he' : r₂.words (rb + j) = normalized true m values j := by
      simpa [b, sourceState, savedState, s₁, Store.ofState, RAMState.setIndex, RAMState.setWord,
        show rb + j ≠ 20 by omega, hvalues₁ j hj] using he
    simpa [t, c, savedState, s₂, Store.ofState, RAMState.setWord, RAMState.setIndex,
      show rb + j ≠ 21 by omega] using he'
  · intro j hj
    simpa [t, c, savedState, s₂, Store.ofState, RAMState.setWord, RAMState.setIndex,
      show vb + j ≠ 21 by omega] using hvalues₂ j hj
  · simpa [t, c, savedState, s₂, Store.ofState, RAMState.setWord, RAMState.setIndex] using scale20
  · simpa [t, c, savedState, s₂, Store.ofState, RAMState.setWord, RAMState.setIndex] using hscale₂
  · intro i hi h24 h26 h55
    by_cases h25 : i = 25
    · subst i
      have he := hf₂.indices 55 (by omega) (by omega)
      simpa [t, c, savedState, s₂, b, sourceState, s₁, Store.ofState, RAMState.setIndex,
        RAMState.setWord, m55] using he
    · have he := hf₂.indices i hi h24
      simpa [t, c, savedState, s₂, b, sourceState, s₁, Store.ofState, RAMState.setIndex,
        RAMState.setWord, h25, h26, mi i hi h24 h26 h55] using he
  · exact hf₂.output.trans hf₁.output
  · exact hf₂.indexOutput.trans hf₁.indexOutput
  · exact hf₂.randomCursor.trans hf₁.randomCursor

end Maxwell.Cost.RealSourceNormalize
