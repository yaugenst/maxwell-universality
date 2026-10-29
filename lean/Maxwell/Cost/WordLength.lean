import Maxwell.Cost.Increment
import Maxwell.Cost.WordTransfer
import Maxwell.Cost.CanonicalBits
import Maxwell.Cost.Structured.Primitive

/-! A finite tape scan computes word length by physical binary increments.
The source contents are preserved and both heads return to their origins.
The word may be empty, all zero, padded, or canonical. -/

namespace Maxwell.Cost.WordLength

private theorem canonical_cons (b : Bool) (xs : List Bool)
    (hc : TapeOps.CanonicalBits xs) (hn : xs ≠ []) : TapeOps.CanonicalBits (b :: xs) := by
  rcases hc with h | ⟨ys, h⟩
  · exact (hn h).elim
  · exact Or.inr ⟨b :: ys, by simp [h]⟩

private theorem carry_canonical_append (carry : Bool) (xs : List Bool) :
    TapeOps.CanonicalBits (Increment.carryBits carry (xs ++ [true])) := by
  induction xs generalizing carry with
  | nil =>
    cases carry
    · exact Or.inr ⟨[], rfl⟩
    · exact Or.inr ⟨[false], rfl⟩
  | cons b xs ih =>
    apply canonical_cons _ _ (ih (b && carry))
    intro heq
    have hlen := Increment.carryBits_length_ge (b && carry) (xs ++ [true])
    simp [heq] at hlen

private theorem increment_canonical (xs : List Bool) (hc : TapeOps.CanonicalBits xs) :
    TapeOps.CanonicalBits (Increment.bits xs) := by
  rcases hc with rfl | ⟨ys, rfl⟩
  · exact Or.inr ⟨[], rfl⟩
  · exact carry_canonical_append true ys

def countBits : ℕ → List Bool
  | 0 => []
  | n + 1 => Increment.bits (countBits n)

theorem countBits_length (n : ℕ) : (countBits n).length ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => exact (Increment.bits_length_le _).trans (Nat.add_le_add_right ih 1)

theorem countBits_value (n : ℕ) : addressValue (countBits n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [countBits, Increment.bits_value, ih]

theorem countBits_canonical (n : ℕ) : TapeOps.CanonicalBits (countBits n) := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih => exact increment_canonical _ ih

theorem countBits_eq (n : ℕ) : countBits n = n.bits := by
  rw [← TapeOps.canonicalBits_bits (countBits_canonical n), countBits_value]

def program (source target : ℕ) : BitRAM := ⟨
  [.readTape source 30 31, .branch 31 2 21] ++
  (Increment.program target).code.map (BitRAMInstruction.relocate 2 14) ++
  (Rewind.program target).code.map (BitRAMInstruction.relocate 14 19) ++
  [.tapeRight source, .jump 0] ++
  (Rewind.program source).code.map (BitRAMInstruction.relocate 21 26) ++ [.halt]⟩

theorem increment_contains (source target : ℕ) :
    (program source target).Contains (Increment.program target) 2 14 := by
  intro i; fin_cases i <;> rfl

theorem target_rewind_contains (source target : ℕ) :
    (program source target).Contains (Rewind.program target) 14 19 := by
  intro i; fin_cases i <;> rfl

theorem source_rewind_contains (source target : ℕ) :
    (program source target).Contains (Rewind.program source) 21 26 := by
  intro i; fin_cases i <;> rfl

theorem halt_instruction (source target : ℕ) : (program source target).code[26]? = some .halt := rfl

def Frame (source target : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ source → i ≠ target → t.tapes i = s.tapes i) ∧
  (∀ i, i < 24 ∨ 31 < i → t.registers i = s.registers i)

theorem Frame.refl (source target : ℕ) (s : BitRAMState) : Frame source target s s := by simp [Frame]

theorem Frame.trans {source target : ℕ} {s t u : BitRAMState}
    (h : Frame source target s t) (k : Frame source target t u) : Frame source target s u := by
  refine ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    k.2.2.2.1.trans h.2.2.2.1, k.2.2.2.2.1.trans h.2.2.2.2.1, ?_, ?_⟩
  · intro i hs ht; exact (k.2.2.2.2.2.1 i hs ht).trans (h.2.2.2.2.2.1 i hs ht)
  · intro i hi; exact (k.2.2.2.2.2.2 i hi).trans (h.2.2.2.2.2.2 i hi)

theorem frame_increment (source target : ℕ) {s t : BitRAMState}
    (h : Increment.Frame target s t) : Frame source target s t := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_, ?_⟩
  · intro i _ ht; exact h.2.2.2.2.2.1 i ht
  · intro i hi; exact h.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)

theorem frame_rewind (source target work : ℕ) (hw : work = source ∨ work = target)
    (origin : ℤ) (s : BitRAMState) : Frame source target s (Rewind.finishAt work origin s) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro i hs ht; simp [Rewind.finishAt, show i ≠ work by omega]
  · intro i hi; simp [Rewind.finishAt, show i ≠ 24 by omega, show i ≠ 25 by omega]

def checked (s : BitRAMState) (b : Bool) (present : Bool) : BitRAMState :=
  {s with
    pc := if present then 2 else 21
    registers := Function.update (Function.update s.registers 30 b) 31 present}

theorem check_present (source target : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 0) (hr : (s.tapes source).read = some b) :
    PricedSteps ((program source target).next input randomTape) 3 s (checked s b true) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, program, hpc, hr, BitRAMState.setRegister, checked]

theorem check_empty (source target : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hr : (s.tapes source).read = none) :
    PricedSteps ((program source target).next input randomTape) 3 s (checked s false false) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, program, hpc, hr, BitRAMState.setRegister, checked]

theorem checked_frame (source target : ℕ) (s : BitRAMState) (b present : Bool) :
    Frame source target s (checked s b present) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, ?_⟩
  intro i hi
  simp [checked, show i ≠ 30 by omega, show i ≠ 31 by omega]

def advance (source : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 0
    tapes := Function.update s.tapes source
      {s.tapes source with head := (s.tapes source).head + 1}}

theorem advance_block (source target : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) : PricedSteps ((program source target).next input randomTape)
      2 {s with pc := 19} (advance source s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, program, Increment.program, Rewind.program,
    BitRAMInstruction.relocate, BitRAMState.setTape, advance]

theorem advance_frame (source target : ℕ) (s : BitRAMState) : Frame source target s (advance source s) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun _ _ => rfl⟩
  intro i hi _; simp [advance, hi]

def cursor (word : List Bool) (origin : ℤ) (position : ℕ) : BitTape :=
  {BitTape.shifted word origin with head := origin + position}

theorem cursor_read (preceding rest : List Bool) (origin : ℤ) :
    (cursor (preceding ++ rest) origin preceding.length).read = rest.head? := by
  simp [cursor, BitTape.read, BitTape.shifted, List.getElem?_append, List.head?_eq_getElem?]

theorem loop (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool)
    (remaining preceding : List Bool) (sourceOrigin targetOrigin : ℤ)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hs : s.tapes source = cursor (preceding ++ remaining) sourceOrigin preceding.length)
    (ht : s.tapes target = BitTape.shifted (countBits preceding.length) targetOrigin) :
    ∃ cost t,
      PricedSteps ((program source target).next input randomTape) cost s t ∧
      cost ≤ remaining.length * (12 * (preceding.length + remaining.length) + 23) +
        4 * (preceding.length + remaining.length) + 9 ∧
      t.pc = 26 ∧ t.tapes source = BitTape.shifted (preceding ++ remaining) sourceOrigin ∧
      t.tapes target = BitTape.shifted (countBits (preceding.length + remaining.length)) targetOrigin ∧
      Frame source target s t := by
  induction remaining generalizing preceding s with
  | nil =>
    let c := {checked s false false with pc := 0}
    have hc := check_empty source target input randomTape s hpc (by rw [hs, cursor_read]; rfl)
    have hword : c.tapes source = BitTape.shiftedEnd preceding sourceOrigin := by
      simpa [c, checked, cursor, BitTape.shiftedEnd] using hs
    obtain ⟨hr, hrword⟩ := WordTransfer.rewind_shifted source sourceOrigin input randomTape preceding c rfl hword
    have hp := (source_rewind_contains source target).call input randomTape hr
      (by simp [Rewind.program, Rewind.finishAt])
    have htarget : (Rewind.finishAt source sourceOrigin c).tapes target =
        BitTape.shifted (countBits preceding.length) targetOrigin := by
      simpa [Rewind.finishAt, c, checked, Ne.symm hne] using ht
    refine ⟨3 + (4 * preceding.length + 5 + 1),
      {Rewind.finishAt source sourceOrigin c with pc := 26}, hc.trans hp,
      by simp; omega, rfl, by simpa using hrword, by simpa using htarget, ?_⟩
    exact (checked_frame source target s false false).trans
      (frame_rewind source target source (Or.inl rfl) sourceOrigin c)
  | cons b remaining ih =>
    let c := {checked s b true with pc := 0}
    have hc := check_present source target input randomTape s b hpc (by rw [hs, cursor_read]; rfl)
    obtain ⟨incCost, u, hcost, hu, hupc, hutarget, huframe⟩ :=
      Increment.simulation target input randomTape (countBits preceding.length) targetOrigin c rfl ht
    have hup := (increment_contains source target).call input randomTape hu
      (by simp [Increment.program, hupc])
    let r := {u with pc := 0}
    obtain ⟨hr, hrtarget⟩ := WordTransfer.rewind_shifted target targetOrigin input randomTape
      (Increment.bits (countBits preceding.length)) r rfl hutarget
    have hrp := (target_rewind_contains source target).call input randomTape hr
      (by simp [Rewind.program, Rewind.finishAt])
    let v := Rewind.finishAt target targetOrigin r
    have hvs : v.tapes source = s.tapes source := by
      have hh := huframe.2.2.2.2.2.1 source hne
      simpa [v, Rewind.finishAt, r, c, checked, hne] using hh
    have hadv := advance_block source target input randomTape v
    have hsource : (advance source v).tapes source =
        cursor ((preceding ++ [b]) ++ remaining) sourceOrigin (preceding ++ [b]).length := by
      simp [advance, hvs, hs, cursor, List.append_assoc, Nat.cast_add, add_assoc]
    have htarget : (advance source v).tapes target =
        BitTape.shifted (countBits (preceding ++ [b]).length) targetOrigin := by
      simpa [advance, Ne.symm hne, v, countBits] using hrtarget
    obtain ⟨restCost, t, hrest, hrestCost, htpc, hts, htt, hframe⟩ :=
      ih (preceding ++ [b]) (advance source v) rfl hsource htarget
    have hall := (((hc.trans hup).trans hrp).trans hadv).trans hrest
    refine ⟨_, t, hall, ?_, htpc, ?_, ?_, ?_⟩
    · have hlen := Increment.bits_length_le (countBits preceding.length)
      have hcountLen := countBits_length preceding.length
      simp only [List.length_append, List.length_cons, List.length_nil] at hrestCost ⊢
      nlinarith
    · simpa [List.append_assoc] using hts
    · simpa [List.length_append, add_assoc, add_comm, add_left_comm] using htt
    · exact ((((checked_frame source target s b true).trans
        (frame_increment source target huframe)).trans
        (frame_rewind source target target (Or.inr rfl) targetOrigin r)).trans
        (advance_frame source target v)).trans hframe

theorem simulation (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (word : List Bool)
    (sourceOrigin targetOrigin : ℤ) (s : BitRAMState) (hpc : s.pc = 0)
    (hs : s.tapes source = BitTape.shifted word sourceOrigin)
    (ht : s.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ cost t,
      PricedSteps ((program source target).next input randomTape) cost s t ∧
      cost ≤ 48 * (word.length + 1) ^ 2 ∧ t.pc = 26 ∧
      t.tapes source = BitTape.shifted word sourceOrigin ∧
      t.tapes target = BitTape.shifted word.length.bits targetOrigin ∧ Frame source target s t := by
  obtain ⟨cost, t, hr, hb, hp, hs', ht', hf⟩ :=
    loop source target hne input randomTape word [] sourceOrigin targetOrigin s hpc
      (by simpa [cursor, BitTape.shifted] using hs) (by simpa [countBits] using ht)
  refine ⟨cost, t, hr, ?_, hp, by simpa using hs', ?_, hf⟩
  · simp only [List.length_nil, zero_add] at hb
    nlinarith
  · simpa [countBits_eq] using ht'

def code (source target : ℕ) : Structured.Code := .call (program source target)

theorem executes (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (word : List Bool)
    (sourceOrigin targetOrigin : ℤ) (s : Structured.Store)
    (hs : s.val.tapes source = BitTape.shifted word sourceOrigin)
    (ht : s.val.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ cost t,
      Structured.Executes input randomTape (code source target) cost s t ∧
      cost ≤ 48 * (word.length + 1) ^ 2 + 1 ∧
      t.val.tapes source = BitTape.shifted word sourceOrigin ∧
      t.val.tapes target = BitTape.shifted word.length.bits targetOrigin ∧ Frame source target s.val t.val := by
  obtain ⟨cost, t, hr, hb, hp, hs', ht', hf⟩ := simulation source target hne input randomTape
    word sourceOrigin targetOrigin s.val s.property hs ht
  refine ⟨cost + 1, Structured.Store.ofState t,
    Structured.Executes.call _ s t cost hr (by rw [hp]; exact halt_instruction source target),
    by omega, hs', ht', hf⟩

theorem run (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (word : List Bool)
    (sourceOrigin targetOrigin : ℤ) (s : BitRAMState) (hpc : s.pc = 0)
    (hs : s.tapes source = BitTape.shifted word sourceOrigin)
    (ht : s.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ t,
      (runPriced ((program source target).next input randomTape)
        (48 * (word.length + 1) ^ 2 + 1) s).finished = some t ∧
      (runPriced ((program source target).next input randomTape)
        (48 * (word.length + 1) ^ 2 + 1) s).instructions ≤ 48 * (word.length + 1) ^ 2 ∧
      t.tapes source = BitTape.shifted word sourceOrigin ∧
      t.tapes target = BitTape.shifted word.length.bits targetOrigin ∧ Frame source target s t := by
  obtain ⟨cost, t, hr, hb, hp, hs', ht', hf⟩ :=
    simulation source target hne input randomTape word sourceOrigin targetOrigin s hpc hs ht
  obtain ⟨hfinished, hcost⟩ := hr.runPriced_ge
    (by simp [BitRAM.next, hp, halt_instruction]) (48 * (word.length + 1) ^ 2 + 1) (by omega)
  exact ⟨t, hfinished, hcost.trans_le hb, hs', ht', hf⟩

end Maxwell.Cost.WordLength
