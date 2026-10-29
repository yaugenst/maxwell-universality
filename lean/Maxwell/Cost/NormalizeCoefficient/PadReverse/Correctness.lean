import Maxwell.Cost.NormalizeCoefficient.PadReverse.Loop
import Maxwell.Cost.RationalAccumulator.Bank

namespace Maxwell.Cost.NormalizeCoefficient.PadReverse

open Structured RationalAccumulator

def code : Code := .seq (.call program) (.call (Rewind.program 82))

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ 4 → i ≠ 83 → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

/-- Padding and reversal cost fifteen charged instructions per emitted bit.
The stored power determines the width through ordinary reads, and is restored. -/
theorem executes (input : List Bool) (tape : ℕ → Bool) (width n : ℕ)
    (hwidth : n.bits.length ≤ width) (s : Store)
    (hn : Word s.val 4 n) (hp : Word s.val 82 (2^width)) (hb : Blank s.val 83) :
    ∃ t : Store, Executes input tape code (15*width+10) s t ∧
      Blank t.val 4 ∧
      (∃ origin, t.val.tapes 83 = BitTape.shifted (padded width n.bits).reverse origin) ∧
      Frame s.val t.val := by
  obtain ⟨so, hsource⟩ := hn
  obtain ⟨po, hpower⟩ := hp
  obtain ⟨dst, htarget⟩ := hb
  let cells := (BitTape.shifted (2^width).bits po).cells
  have hfalse : ∀ k : ℕ, k < width → cells (po+k) = some false := by
    intro k hk
    simp [cells, BitTape.shifted, PowerOfTwo.power_bits, List.getElem?_append, hk]
  have htrue : cells (po+width) = some true := by
    simp [cells, BitTape.shifted, PowerOfTwo.power_bits, List.getElem?_append]
  obtain ⟨w, hw, hpc, hw4, hw83, hw82, hwf⟩ := loop input tape width n.bits [] hwidth
    so dst po cells s.val s.property hsource (by simpa using htarget) hpower hfalse htrue
  let a : Store := Store.ofState w
  have ha : Executes input tape (.call program) (11*width+4) s a :=
    Executes.call _ _ _ _ hw (by simp [program, hpc])
  have hrewind := Rewind.stepsAt 82 po input tape width a.val a.property
    (by simp [a, Store.ofState, hw82])
    (by simp [a, Store.ofState, hw82, cells, BitTape.shifted])
    (by intro k hk; exact ⟨false, by simpa [a, Store.ofState, hw82] using hfalse k hk⟩)
  let t := Store.ofState (Rewind.finishAt 82 po a.val)
  have ht : Executes input tape (.call (Rewind.program 82)) (4*width+6) a t :=
    Executes.call _ _ _ _ hrewind (by simp [Rewind.program, Rewind.finishAt])
  have ht82 : t.val.tapes 82 = s.val.tapes 82 := by
    simp [t, a, Store.ofState, Rewind.finishAt, hw82, hpower, cells, BitTape.shifted]
  refine ⟨t, ?_, ⟨so+width, ?_⟩, ⟨dst-width, ?_⟩, ?_⟩
  · convert ha.seq ht using 1 <;> first | rfl | omega
  · simpa [t, a, Store.ofState, Rewind.finishAt] using hw4
  · simpa [t, a, Store.ofState, Rewind.finishAt] using hw83
  · rcases hwf with ⟨ha, hi, hm, hr, ho, htapes, hg⟩
    refine ⟨ha, hi, hm, hr, ho, ?_, ?_⟩
    · intro i h4 h83
      by_cases h82 : i = 82
      · subst i; exact ht82
      · simpa [t, a, Store.ofState, Rewind.finishAt, h82] using htapes i h4 h82 h83
    · intro i h24 h25 h26 h27 h28 h29
      simpa [t, a, Store.ofState, Rewind.finishAt, h24, h25] using hg i h26 h27 h28 h29

theorem compiled_run (input : List Bool) (tape : ℕ → Bool) (width n : ℕ)
    (hwidth : n.bits.length ≤ width) (s : Store)
    (hn : Word s.val 4 n) (hp : Word s.val 82 (2^width)) (hb : Blank s.val 83) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape) (15*width+11) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (15*width+11) s.val).instructions = 15*width+10 ∧
      Blank t.val 4 ∧
      (∃ origin, t.val.tapes 83 = BitTape.shifted (padded width n.bits).reverse origin) ∧
      Frame s.val t.val := by
  obtain ⟨t, he, h4, h83, hf⟩ := executes input tape width n hwidth s hn hp hb
  have hr := he.compiled_run (15*width+11) (by omega)
  exact ⟨t, hr.1, hr.2, h4, h83, hf⟩

end Maxwell.Cost.NormalizeCoefficient.PadReverse
