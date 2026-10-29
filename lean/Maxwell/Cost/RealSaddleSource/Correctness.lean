import Maxwell.Cost.RealSaddleSource.Program

namespace Maxwell.Cost.RealSaddleSource
open RealSimulation.Control
set_option maxRecDepth 20000

/-- A genuine addressed source assembly: zero the full vector, then load,
negate, and store the preserved transpose product into its middle block. -/
theorem executes (input : RAMInput) (tape : ℕ → Bool)
    (src dst rows columns padding : ℕ) (q : ℕ → ℝ) (s : Store)
    (hsrc : 8 ≤ src) (hsep : src + columns ≤ dst)
    (hr : s.val.indices 70 = rows) (hc : s.val.indices 71 = columns)
    (hp : s.val.indices 72 = padding) (hs : s.val.indices 80 = src)
    (hd : s.val.indices 54 = dst) (hq : ∀ j < columns, s.val.words (src + j) = q j) :
    ∃ t : Store, Executes input tape code (5 * (rows + columns + padding) + 8 * columns + 21) s t ∧
      (∀ j < rows + columns + padding, t.val.words (dst + j) = rhs rows columns q j) ∧
      (∀ j < columns, t.val.words (src + j) = q j) ∧
      Frame dst (rows + columns + padding) s.val t.val := by
  let a := zeroPrepared s
  obtain ⟨b, heb, hzero, hfzero⟩ := RealArrayZero.executes input tape dst (rows + columns + padding) a
    (by simp [a, zeroPrepared, Store.ofState, RAMState.setIndex, hd])
    (by simp [a, zeroPrepared, Store.ofState, RAMState.setIndex, hr, hc, hp])
  have hmeta (i : ℕ) (hi : 4 ≤ i) (hi₁ : i ≠ 56) (hi₂ : i ≠ 57) :
      b.val.indices i = s.val.indices i := by
    simpa [a, zeroPrepared, Store.ofState, RAMState.setIndex, hi₁, hi₂] using hfzero.indices i hi
  let c := copyPrepared b
  have hqc : ∀ j < columns, c.val.words (src + j) = q j := by
    intro j hj
    exact (hfzero.words (src + j) (by omega) (Or.inl (by omega))).trans (hq j hj)
  obtain ⟨t, het, hcopy, hinput, hfcopy⟩ := RealArrayCopy.executes true input tape src (dst + rows) columns q c
    hsrc (by omega)
    (by simp [c, copyPrepared, Store.ofState, RAMState.setIndex, hmeta 80 (by omega) (by omega) (by omega), hs])
    (by simp [c, copyPrepared, Store.ofState, RAMState.setIndex,
      hmeta 54 (by omega) (by omega) (by omega), hd, hmeta 70 (by omega) (by omega) (by omega), hr])
    (by simp [c, copyPrepared, Store.ofState, RAMState.setIndex, hmeta 71 (by omega) (by omega) (by omega), hc]) hqc
  refine ⟨t, ?_, ?_, hinput, ?_⟩
  · convert (prepareZero_executes input tape s).seq
      (heb.seq ((prepareCopy_executes input tape b).seq het)) using 1 <;> try rfl
    omega
  · intro j hj
    by_cases hjr : j < rows
    · have he := hfcopy.words (dst + j) (by omega) (Or.inl (by omega))
      change t.val.words (dst + j) = b.val.words (dst + j) at he
      rw [he, hzero j hj]
      simp [rhs, hjr]
    · by_cases hjc : j < rows + columns
      · have hk : j - rows < columns := by omega
        have he := hcopy (j - rows) hk
        have hadd : dst + rows + (j - rows) = dst + j := by omega
        simpa [rhs, hjr, hjc, hadd, RealArrayCopy.sign] using he
      · have he := hfcopy.words (dst + j) (by omega) (Or.inr (by omega))
        change t.val.words (dst + j) = b.val.words (dst + j) at he
        rw [he, hzero j hj]
        simp [rhs, hjr, hjc]
  · refine ⟨?_, ?_, hfcopy.output.trans hfzero.output,
      hfcopy.indexOutput.trans hfzero.indexOutput, hfcopy.randomCursor.trans hfzero.randomCursor⟩
    · intro i hi hout
      have ho : i < dst + rows ∨ dst + rows + columns ≤ i := by omega
      exact (hfcopy.words i hi ho).trans (hfzero.words i (by omega) hout)
    · intro i hi h55 h56 h57
      have he := hfcopy.indices i hi
      simp only [c, copyPrepared, Store.ofState, RAMState.setIndex] at he
      simp only [Function.update_of_ne h55, Function.update_of_ne h56, Function.update_of_ne h57] at he
      exact he.trans (hmeta i hi h56 h57)

theorem run (input : RAMInput) (tape : ℕ → Bool)
    (src dst rows columns padding : ℕ) (q : ℕ → ℝ) (s : Store)
    (hsrc : 8 ≤ src) (hsep : src + columns ≤ dst)
    (hr : s.val.indices 70 = rows) (hc : s.val.indices 71 = columns)
    (hp : s.val.indices 72 = padding) (hs : s.val.indices 80 = src)
    (hd : s.val.indices 54 = dst) (hq : ∀ j < columns, s.val.words (src + j) = q j) :
    ∃ t : RAMState,
      (runCapped (program.next input tape) (5 * (rows + columns + padding) + 8 * columns + 22) s.val).finished = some t ∧
      (runCapped (program.next input tape) (5 * (rows + columns + padding) + 8 * columns + 22) s.val).instructions =
        5 * (rows + columns + padding) + 8 * columns + 21 ∧
      (∀ j < rows + columns + padding, t.words (dst + j) = rhs rows columns q j) ∧
      (∀ j < columns, t.words (src + j) = q j) ∧ Frame dst (rows + columns + padding) s.val t := by
  obtain ⟨t, ht, hv, hq, hf⟩ := executes input tape src dst rows columns padding q s hsrc hsep hr hc hp hs hd hq
  obtain ⟨hcap, hcost⟩ := ht.compiled_run (5 * (rows + columns + padding) + 8 * columns + 22) (by omega)
  exact ⟨t.place code.size, hcap, hcost, hv, hq,
    ⟨hf.words, hf.indices, hf.output, hf.indexOutput, hf.randomCursor⟩⟩

end Maxwell.Cost.RealSaddleSource
