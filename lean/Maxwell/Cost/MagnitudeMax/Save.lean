import Maxwell.Cost.MagnitudeMax.Parse

namespace Maxwell.Cost.MagnitudeMax.Save

open Structured RationalAccumulator

/-- Copy an arithmetic word into a persistent tape without changing the
source. Its width is read by the finite clone routine. -/
theorem clone (source target n : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hsource : Word s.val source n) (hblank : Blank s.val target) :
    ∃ t : Store, Executes input tape (.call (WordTransfer.clone source target))
      (15 * n.bits.length + 17) s t ∧ Word t.val target n ∧
      t.val.inputHead = s.val.inputHead ∧ DecoderParser.Frame {target} s.val t.val := by
  obtain ⟨origin, hs⟩ := hsource
  obtain ⟨destination, hd⟩ := hblank
  obtain ⟨t, ht, hpc, hsource', htarget, hf⟩ := WordTransfer.clone_steps source target hne input tape
    n.bits origin destination s.val s.property hs hd
  refine ⟨Store.ofState t, Executes.call _ _ _ _ ht (by
    simp [WordTransfer.clone, hpc, Copy.program, Rewind.program, BitRAMInstruction.relocate]),
    ⟨destination, htarget⟩, hf.2.1, hf.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, ?_⟩
  intro i hi
  have htarget' : i ≠ target := by simpa using hi
  by_cases hsource'' : i = source
  · subst i
    exact hsource'.trans hs.symm
  · exact hf.2.2.2.2.2.1 i hsource'' htarget'

def code (numerator denominator : ℕ) : Code :=
  .seq (.call (WordTransfer.clone 30 numerator)) (.call (WordTransfer.clone 31 denominator))

theorem pair (numerator denominator : ℕ) (hn : 36 < numerator) (hd : 36 < denominator)
    (hne : numerator ≠ denominator) (p : Pair) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hnum : Word s.val 30 p.1) (hden : Word s.val 31 p.2)
    (hblankN : Blank s.val numerator) (hblankD : Blank s.val denominator) :
    ∃ t : Store, Executes input tape (code numerator denominator)
      (15 * (p.1.bits.length + p.2.bits.length) + 34) s t ∧
      Word t.val numerator p.1 ∧ Word t.val denominator p.2 ∧
      t.val.inputHead = s.val.inputHead ∧ DecoderParser.Frame {numerator, denominator} s.val t.val := by
  obtain ⟨u, hu, hun, huh, huf⟩ := clone 30 numerator p.1 (by omega) input tape s hnum hblankN
  obtain ⟨t, ht, htd, hth, htf⟩ := clone 31 denominator p.2 (by omega) input tape u
    (word_of_eq (huf.tapes 31 (by simp; omega)) hden)
    (blank_of_eq (huf.tapes denominator (by simpa using hne.symm)) hblankD)
  refine ⟨t, ?_, word_of_eq (htf.tapes numerator (by simpa using hne)) hun, htd,
    hth.trans huh, ?_⟩
  · convert hu.seq ht using 1 <;> first | rfl | omega
  · refine ⟨htf.address.trans huf.address, htf.memory.trans huf.memory,
      htf.randomCursor.trans huf.randomCursor, htf.output.trans huf.output, ?_⟩
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact (htf.tapes i (by simpa using hi.2)).trans (huf.tapes i (by simpa using hi.1))

end Maxwell.Cost.MagnitudeMax.Save
