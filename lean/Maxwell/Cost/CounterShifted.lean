import Maxwell.Cost.Counter
import Maxwell.Cost.Multiplication.Tapes

namespace Maxwell.Cost

/-- Same-width replacement at an arbitrary integer tape origin. -/
theorem TapeWrites.shifted_same_width {xs ys : List Bool} {origin : ℤ} {after : BitTape}
    (h : TapeWrites (BitTape.shifted xs origin) after ys) (hlen : ys.length = xs.length) :
    after = BitTape.shiftedEnd ys origin := by
  apply BitTape.ext
  · simpa [BitTape.shifted, BitTape.shiftedEnd] using h.head
  · funext p
    rw [h.cells]
    change writeCells (BitTape.shifted xs origin).cells origin ys p =
      (BitTape.shiftedEnd ys origin).cells p
    by_cases hp : p < origin
    · rw [writeCells_preserves_left _ _ _ _ hp]
      simp [BitTape.shiftedEnd, BitTape.shifted, show ¬origin ≤ p by omega]
    · have hnonneg : origin ≤ p := by omega
      have hnat : origin + ((p - origin).toNat : ℤ) = p := by omega
      by_cases hk : (p - origin).toNat < ys.length
      · have hh := writeCells_read (BitTape.shifted xs origin).cells origin ys (p - origin).toNat hk
        simpa [BitTape.shiftedEnd, BitTape.shifted, hnat, hnonneg] using hh
      · rw [writeCells_preserves_right _ _ _ _ (by omega)]
        simp [BitTape.shiftedEnd, BitTape.shifted, hnonneg,
          List.getElem?_eq_none (by omega : xs.length ≤ (p - origin).toNat),
          List.getElem?_eq_none (by omega : ys.length ≤ (p - origin).toNat)]

namespace CounterShifted

theorem steps (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (origin : ℤ)
    (initial : BitRAMState) (hpc : initial.pc = 0)
    (hword : initial.tapes 0 = BitTape.shifted xs origin) :
    ∃ final, PricedSteps (Counter.program.next input tape) (13 * xs.length + 11) initial final ∧
      final.pc = 15 ∧ final.tapes 0 = BitTape.shifted (subtractBit true xs) origin ∧
      (final.registers 2 = true ↔ addressValue xs = 0) ∧ Counter.Frame initial final := by
  obtain ⟨s, hs, hspc, _, hwrites, hzero, _⟩ := binaryCounter_simulation input tape initial xs hpc
    (hword ▸ BitTape.shifted_represents xs origin)
  have hframe := binaryCounter_steps_frame input tape hs
  have hstape : s.tapes 0 = BitTape.shiftedEnd (subtractBit true xs) origin := by
    rw [hword] at hwrites
    exact hwrites.shifted_same_width (subtractBit_length true xs)
  have hsLinked := hs.link [] 10 Counter.counterSuffix
  simp only [List.length_nil, BitRAMState.relocate, Nat.zero_add] at hsLinked
  change PricedSteps (Counter.program.next input tape) _ initial s at hsLinked
  have hsReturn : PricedSteps (Counter.program.next input tape) 1 s {s with pc := 10} := by
    simpa only [List.length_nil, BitRAMState.relocate, Nat.zero_add, Counter.program] using
      (PricedSteps.step (BitRAM.link_return [] binaryCounter 10 Counter.counterSuffix input tape s
        (by simp [binaryCounter, hspc])) (PricedSteps.refl _))
  let rewindStart := {s with pc := 0}
  have hr := Rewind.shiftedEnd_steps 0 origin input tape (subtractBit true xs) rewindStart rfl hstape
  have hrLinked := hr.link Counter.rewindPreamble 15 [.halt]
  rw [← Counter.program_as_rewind, Counter.rewindPreamble_length] at hrLinked
  have hstart : rewindStart.relocate 10 = {s with pc := 10} := by
    simp [rewindStart, BitRAMState.relocate]
  rw [hstart] at hrLinked
  let result := Rewind.finishAt 0 origin rewindStart
  have hrReturn : PricedSteps (Counter.program.next input tape) 1
      (result.relocate 10) {result with pc := 15} := by
    rw [Counter.program_as_rewind]
    simpa only [Counter.rewindPreamble_length] using
      (PricedSteps.step (BitRAM.link_return Counter.rewindPreamble (Rewind.program 0) 15 [.halt]
        input tape result (by simp [result, Rewind.finishAt, Rewind.program])) (PricedSteps.refl _))
  have hall : PricedSteps (Counter.program.next input tape) (13 * xs.length + 11)
      initial {result with pc := 15} := by
    convert ((hsLinked.trans hsReturn).trans hrLinked).trans hrReturn using 1
    simp
    omega
  refine ⟨{result with pc := 15}, hall, rfl, ?_, ?_, ?_⟩
  · exact Rewind.finishAt_shiftedEnd 0 origin _ rewindStart hstape
  · simpa [result, Rewind.finishAt] using hzero
  · rcases hframe with ⟨ha, hi, hm, hr, ho, ht, hg⟩
    refine ⟨ha, hi, hm, hr, ho, ?_, ?_⟩
    · intro i hne
      simpa [result, Rewind.finishAt, rewindStart, hne] using ht i hne
    · intro i hgt h24 h25
      simpa [result, Rewind.finishAt, rewindStart, h24, h25] using hg i hgt

theorem steps_on (workTape : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (xs : List Bool) (origin : ℤ) (initial : BitRAMState) (hpc : initial.pc = 0)
    (hword : initial.tapes workTape = BitTape.shifted xs origin) :
    ∃ final, PricedSteps ((Counter.programOn workTape).next input tape)
        (13 * xs.length + 11) initial final ∧
      final.pc = 15 ∧ final.tapes workTape = BitTape.shifted (subtractBit true xs) origin ∧
      (final.registers 2 = true ↔ addressValue xs = 0) ∧ Counter.FrameAt workTape initial final := by
  let p : Equiv.Perm ℕ := Equiv.swap 0 workTape
  obtain ⟨s, hs, hspc, hsword, hzero, hframe⟩ :=
    steps input tape xs origin (initial.renameTapes p.symm) hpc
      (by simpa [BitRAMState.renameTapes, p] using hword)
  have hinverse : (initial.renameTapes p.symm).renameTapes p = initial := by
    cases initial
    simp [BitRAMState.renameTapes, Function.comp_def]
  have hrenamed := hs.renameTapes p
  rw [hinverse] at hrenamed
  refine ⟨s.renameTapes p, hrenamed, hspc, ?_, hzero, ?_⟩
  · simpa [BitRAMState.renameTapes, p] using hsword
  · rcases hframe with ⟨ha, hi, hm, hr, ho, ht, hg⟩
    refine ⟨ha, hi, hm, hr, ho, ?_, hg⟩
    intro i hne
    have hp : p.symm i ≠ 0 := by
      intro heq
      have hh := congrArg p heq
      simp [p] at hh
      exact hne hh
    simpa [BitRAMState.renameTapes, Function.comp_def] using ht (p.symm i) hp

end CounterShifted
end Maxwell.Cost
