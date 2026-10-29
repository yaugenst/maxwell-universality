import Maxwell.Cost.FixedWidth
import Maxwell.Cost.SourceCircuit.ReverseBits

namespace Maxwell.Cost.CalibrationMatrix

open Structured

/-- Only the output tape and the six loop registers may change. -/
structure PadWordFrame (target : ℕ) (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ≠ target → t.tapes i = s.tapes i
  registers : ∀ i, i < 26 ∨ 31 < i → t.registers i = s.registers i

private structure RewindFrame (source clock target : ℕ) (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ≠ source → i ≠ clock → i ≠ target → t.tapes i = s.tapes i
  registers : ∀ i, i ≠ 30 → i ≠ 31 → t.registers i = s.registers i

private def rewindPairBody (source target : ℕ) : Code :=
  .seq (.atom (.tapeLeft source)) (.atom (.tapeLeft target))

/-- The clock, rather than the source contents, controls all return moves.
This restores the source even when it is empty or shorter than the width. -/
def padWordCode (source clock target : ℕ) : Code :=
  .seq (.call (FixedWidth.program source clock target))
    (SourceCircuit.ReverseBits.code clock (rewindPairBody source target))

private theorem rewind_pair (source clock target : ℕ)
    (hsc : source ≠ clock) (hst : source ≠ target) (hct : clock ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (word xs ys : List Bool)
    (so co targetOrigin : ℤ) (s : Store)
    (hs : s.val.tapes source = {BitTape.shifted xs so with head := so + word.length})
    (hc : s.val.tapes clock = BitTape.shiftedEnd word co)
    (ht : s.val.tapes target = {BitTape.shifted ys targetOrigin with
      head := targetOrigin + word.length}) :
    ∃ cost t, cost ≤ 10*word.length+8 ∧
      Executes input randomTape
        (SourceCircuit.ReverseBits.code clock (rewindPairBody source target)) cost s t ∧
      t.val.tapes source = BitTape.shifted xs so ∧
      t.val.tapes clock = BitTape.shifted word co ∧
      t.val.tapes target = BitTape.shifted ys targetOrigin ∧
      RewindFrame source clock target s.val t.val := by
  let inv : List Bool → Unit → Store → Prop := fun remaining _ t =>
    t.val.tapes source = {BitTape.shifted xs so with head := so + remaining.length} ∧
    t.val.tapes target = {BitTape.shifted ys targetOrigin with
      head := targetOrigin + remaining.length} ∧ RewindFrame source clock target s.val t.val
  have stable : ∀ bits data a b, SourceCircuit.ScanBits.Passive clock a b →
      inv bits data a → inv bits data b := by
    intro bits data a b hf hi
    rcases hi with ⟨has, hat, ha⟩
    exact ⟨(hf.tapes source hsc).trans has, (hf.tapes target hct.symm).trans hat,
      ⟨hf.address.trans ha.address, hf.memory.trans ha.memory,
        hf.inputHead.trans ha.inputHead, hf.randomCursor.trans ha.randomCursor,
        hf.output.trans ha.output,
        fun i his hic hit => (hf.tapes i hic).trans (ha.tapes i his hic hit),
        fun i h30 h31 => (hf.registers i h30 h31).trans (ha.registers i h30 h31)⟩⟩
  have bodyCorrect : ∀ bits bit data a, inv (bits ++ [bit]) data a →
      a.val.registers 30 = bit → a.val.registers 31 = true →
      ∃ cost b, cost ≤ 4 ∧ Executes input randomTape (rewindPairBody source target) cost a b ∧
        inv bits data b ∧ b.val.tapes clock = a.val.tapes clock := by
    intro bits bit data a hi _ _
    rcases hi with ⟨has, hat, ha⟩
    let b := SourceCircuit.ReverseBits.retreated source a
    let c := SourceCircuit.ReverseBits.retreated target b
    have keep (i : ℕ) (his : i ≠ source) (hit : i ≠ target) :
        c.val.tapes i = a.val.tapes i := by
      simp [c, b, SourceCircuit.ReverseBits.retreated, Store.ofState,
        BitRAMState.setTape, his, hit]
    refine ⟨4, c, le_rfl, (Executes.tapeLeft input randomTape a source).seq
      (Executes.tapeLeft input randomTape b target), ?_, keep clock hsc.symm hct⟩
    refine ⟨?_, ?_, ⟨ha.address, ha.memory, ha.inputHead, ha.randomCursor, ha.output,
      fun i his hic hit => (keep i his hit).trans (ha.tapes i his hic hit),
      ha.registers⟩⟩
    · simp [c, b, SourceCircuit.ReverseBits.retreated, Store.ofState,
        BitRAMState.setTape, hst, has, List.length_append, Nat.cast_add, ← add_assoc]
    · simp [c, b, SourceCircuit.ReverseBits.retreated, Store.ofState,
        BitRAMState.setTape, hst.symm, hat, List.length_append, Nat.cast_add, ← add_assoc]
  have hi : inv word () s :=
    ⟨hs, ht, ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩⟩
  obtain ⟨cost, t, hcost, he, hi, hclock⟩ := SourceCircuit.ReverseBits.executes_word
    clock (rewindPairBody source target) (fun _ (_ : Unit) => ()) input randomTape inv
    4 stable bodyCorrect word co () s hc hi
  refine ⟨cost, t, by omega, he, ?_, hclock, ?_, hi.2.2⟩
  · simpa [inv, BitTape.shifted] using hi.1
  · simpa [inv, BitTape.shifted] using hi.2.1

/-- A uniform finite machine pads a word to the stored clock width, returns
the result at its first cell, and restores both input tapes exactly. -/
theorem pad_word_raw (source clock target : ℕ)
    (hsc : source ≠ clock) (hst : source ≠ target) (hct : clock ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (width : ℕ) (clockWord xs : List Bool)
    (hwidth : clockWord.length = width)
    (so co targetOrigin : ℤ) (s : Store)
    (hs : s.val.tapes source = BitTape.shifted xs so)
    (hc : s.val.tapes clock = BitTape.shifted clockWord co)
    (ht : s.val.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ cost t, cost ≤ 20*width+12 ∧
      Executes input randomTape (padWordCode source clock target) cost s t ∧
      t.val.tapes target = BitTape.shifted (FixedWidth.bits width xs) targetOrigin ∧
      t.val.tapes source = s.val.tapes source ∧ t.val.tapes clock = s.val.tapes clock ∧
      PadWordFrame target s.val t.val := by
  obtain ⟨a, ea, pa, has, hac, hat, hf⟩ := FixedWidth.simulation source clock target
    hsc hst hct input randomTape clockWord xs so co targetOrigin s.val s.property hc hs ht
  have ecall : Executes input randomTape (.call (FixedWidth.program source clock target))
      (10*clockWord.length+4) s (Store.ofState a) :=
    .call _ s a _ ea (by rw [pa]; rfl)
  have hat' : (Store.ofState a).val.tapes target =
      {BitTape.shifted (FixedWidth.bits clockWord.length xs) targetOrigin with
        head := targetOrigin + clockWord.length} := by
    simpa [Store.ofState, BitTape.shiftedEnd] using hat
  obtain ⟨cost, t, hcost, er, hsource, hclock, htarget, hr⟩ := rewind_pair
    source clock target hsc hst hct input randomTape clockWord xs
    (FixedWidth.bits clockWord.length xs) so co targetOrigin (Store.ofState a) has hac hat'
  have sourceEq : t.val.tapes source = s.val.tapes source := hsource.trans hs.symm
  have clockEq : t.val.tapes clock = s.val.tapes clock := hclock.trans hc.symm
  refine ⟨10*clockWord.length+4+cost, t, by omega, ecall.seq er,
    by simpa only [hwidth] using htarget, sourceEq, clockEq, ?_⟩
  rcases hf with ⟨fa, fi, fm, fr, fo, ft, fg⟩
  refine ⟨hr.address.trans fa, hr.memory.trans fm, hr.inputHead.trans fi,
    hr.randomCursor.trans fr, hr.output.trans fo, ?_, ?_⟩
  · intro i hit
    by_cases his : i = source
    · subst i; exact sourceEq
    by_cases hic : i = clock
    · subst i; exact clockEq
    exact (hr.tapes i his hic hit).trans (ft i his hic hit)
  · intro i hi
    exact (hr.registers i (by omega) (by omega)).trans
      (fg i (by omega) (by omega) (by omega) (by omega))

theorem pad_word (source clock target : ℕ)
    (hsc : source ≠ clock) (hst : source ≠ target) (hct : clock ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (width : ℕ) (clockWord xs : List Bool)
    (hwidth : clockWord.length = width) (hfit : xs.length ≤ width)
    (so co targetOrigin : ℤ) (s : Store)
    (hs : s.val.tapes source = BitTape.shifted xs so)
    (hc : s.val.tapes clock = BitTape.shifted clockWord co)
    (ht : s.val.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ cost t, cost ≤ 20*width+12 ∧
      Executes input randomTape (padWordCode source clock target) cost s t ∧
      t.val.tapes target = BitTape.shifted (FixedWidth.bits width xs) targetOrigin ∧
      t.val.tapes source = s.val.tapes source ∧ t.val.tapes clock = s.val.tapes clock ∧
      addressValue (FixedWidth.bits width xs) = addressValue xs ∧
      PadWordFrame target s.val t.val := by
  obtain ⟨cost, t, hc, he, htape, hsource, hclock, hf⟩ := pad_word_raw
    source clock target hsc hst hct input randomTape width clockWord xs hwidth
    so co targetOrigin s hs hc ht
  exact ⟨cost, t, hc, he, htape, hsource, hclock, FixedWidth.bits_value width xs hfit, hf⟩

/-- Bank-facing form: the padding machine needs no scratch tapes and leaves
the shared arithmetic workspace untouched when the output is a bank. -/
theorem pad_word_bank (source clock target : ℕ) (htarget : 10 ≤ target)
    (hsc : source ≠ clock) (hst : source ≠ target) (hct : clock ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (width : ℕ) (clockWord xs : List Bool)
    (hwidth : clockWord.length = width) (hfit : xs.length ≤ width)
    (s : Store) (hs : BankArray.Word s.val source xs)
    (hc : BankArray.Word s.val clock clockWord) (ht : RationalAccumulator.Blank s.val target)
    (hscratch : BankArray.Scratch s.val) :
    ∃ cost t, cost ≤ 20*width+12 ∧
      Executes input randomTape (padWordCode source clock target) cost s t ∧
      BankArray.Word t.val target (FixedWidth.bits width xs) ∧
      BankArray.Word t.val source xs ∧ BankArray.Word t.val clock clockWord ∧
      BankArray.Scratch t.val ∧ PadWordFrame target s.val t.val := by
  obtain ⟨so, hs⟩ := hs
  obtain ⟨co, hc⟩ := hc
  obtain ⟨targetOrigin, ht⟩ := ht
  obtain ⟨cost, t, hcost, he, hout, hsource, hclock, _, hf⟩ := pad_word
    source clock target hsc hst hct input randomTape width clockWord xs hwidth hfit
    so co targetOrigin s hs hc ht
  refine ⟨cost, t, hcost, he, ⟨targetOrigin, hout⟩,
    ⟨so, hsource.trans hs⟩, ⟨co, hclock.trans hc⟩, ?_, hf⟩
  exact SourceCircuit.scratch_of_tapes hscratch (fun i hi => hf.tapes i (by omega))

end Maxwell.Cost.CalibrationMatrix
