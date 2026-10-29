import Maxwell.Cost.RationalAccumulator.Bank
import Maxwell.Cost.SignedDifference.Frame
import Maxwell.Cost.EmitRat

namespace Maxwell.Cost.RationalAccumulator

open Structured

def emitPair (v : ℕ → ℕ) (hd : 0 < v 32) : Codec.RationalPair :=
  ⟨(v 30 : ℤ) - v 31, v 32, hd⟩

def emitCode : Code :=
  .seq (.call (WordTransfer.clone 30 0))
    (.seq (.call (WordTransfer.clone 31 1))
      (.seq (.call (WordTransfer.clone 32 3))
        (.seq (.call SignedDifference.program)
          (.seq (.call (Rewind.program 2)) (.call (EmitRat.program 2 3))))))

/-- Emission changes the output channel and scratch registers 23 through 28.
Every persistent tape, including the whole rational bank, remains unchanged. -/
def EmitFrame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧
  (∀ i, 4 ≤ i → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 23 → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 →
    t.registers i = s.registers i)

/-- The operand copies retain their padded cells and exact final head
positions, so an actual rewind and erasure can prepare the next row. -/
def EmitOperands (s : BitRAMState) (p n : ℕ) : Prop :=
  ∃ po no : ℤ,
    s.tapes 0 = {BitTape.shifted (SignedDifference.padded p.bits) po with
      head := po + max (SignedDifference.padded p.bits).length (SignedDifference.padded n.bits).length} ∧
    s.tapes 1 = {BitTape.shifted (SignedDifference.padded n.bits) no with
      head := no + max (SignedDifference.padded p.bits).length (SignedDifference.padded n.bits).length}

theorem EmitFrame.trans {s t u : BitRAMState} (h : EmitFrame s t) (k : EmitFrame t u) :
    EmitFrame s u := by
  rcases h with ⟨ha, hi, hm, hr, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr,
    fun i h4 => (kt i h4).trans (ht i h4),
    fun i h15 h23 h24 h25 h26 h27 h28 =>
      (kg i h15 h23 h24 h25 h26 h27 h28).trans (hg i h15 h23 h24 h25 h26 h27 h28)⟩

private theorem clone_scratch (source target : ℕ) (hs : 4 ≤ source) (ht : target < 4)
    (input : List Bool) (tape : ℕ → Bool) (n : ℕ) (so destOrigin : ℤ) (s : Store)
    (hsource : s.val.tapes source = BitTape.shifted n.bits so)
    (htarget : s.val.tapes target = {BitTape.blank with head := destOrigin}) :
    ∃ t : Store, Executes input tape (.call (WordTransfer.clone source target))
        (15 * n.bits.length + 17) s t ∧
      t.val.tapes target = BitTape.shifted n.bits destOrigin ∧
      (∀ i, i ≠ target → t.val.tapes i = s.val.tapes i) ∧
      t.val.output = s.val.output ∧ EmitFrame s.val t.val := by
  obtain ⟨t, he, hp, hts, htt, hf⟩ := WordTransfer.clone_steps source target (by omega)
    input tape n.bits so destOrigin s.val s.property hsource htarget
  have hother : ∀ i, i ≠ target → t.tapes i = s.val.tapes i := by
    intro i hi
    by_cases his : i = source
    · subst i; exact hts.trans hsource.symm
    · exact hf.2.2.2.2.2.1 i his hi
  refine ⟨Store.ofState t, Executes.call _ _ _ _ he (by
    simp [WordTransfer.clone, hp, Copy.program, Rewind.program, BitRAMInstruction.relocate]),
    htt, hother, hf.2.2.2.2.1, ?_⟩
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1,
    fun i h4 => hother i (by omega),
    fun i _ _ h24 h25 h26 h27 _ => hf.2.2.2.2.2.2 i h24 h25 h26 h27⟩

private theorem difference_frame {s t : BitRAMState} (h : SignedDifference.Frame s t) :
    EmitFrame s t := by
  rcases h with ⟨ha, hi, hm, hr, _, ht, hg⟩
  exact ⟨ha, hi, hm, hr, fun i hi => ht i (by omega),
    fun i h15 h23 h24 h25 h26 h27 _ => hg i h15 h23 h24 h25 h26 h27⟩

private theorem rewind_frame (origin : ℤ) (s : BitRAMState) :
    EmitFrame s (Rewind.finishAt 2 origin s) := by
  simp [EmitFrame, Rewind.finishAt]
  constructor
  · intro i hi; simp [show i ≠ 2 by omega]
  · intro i _ _ h24 h25 _ _ _; simp [h24, h25]

private theorem emit_frame (num den : List Bool) (s : BitRAMState) :
    EmitFrame s (EmitRat.finish 2 3 num den s) := by
  simp [EmitFrame, EmitRat.finish, EmitRat.denominatorStart, EmitRat.numeratorStart,
    EmitNat.finish, EmitNat.payloadStart, EmitNat.rewindStart, EmitNat.separatorStart,
    EmitNat.headerStart, TapeIO.finish, Rewind.finishAt]
  constructor
  · intro i hi; simp [show i ≠ 2 by omega, show i ≠ 3 by omega]
  · intro i _ _ h24 h25 h26 h27 h28; simp [h24, h25, h26, h27, h28]

private theorem canonical_length_le (bs : List Bool) : (addressValue bs).bits.length ≤ bs.length := by
  obtain ⟨core, n, hbs, hc⟩ := TapeOps.trailing_zero_decomposition bs
  rw [hbs, TapeOps.addressValue_append_zeros, TapeOps.canonicalBits_bits hc]
  simp

private theorem magnitude_eq_natAbs (p n : ℕ) :
    addressValue (SignedDifference.magnitude p.bits n.bits) = ((p : ℤ) - n).natAbs := by
  have h := congrArg Int.natAbs (SignedDifference.signed_value p.bits n.bits)
  cases hs : SignedDifference.sign p.bits n.bits <;> simpa [hs] using h

private theorem difference_sign (p n : ℕ) :
    SignedDifference.sign p.bits n.bits = decide ((p : ℤ) - n < 0) := by
  have h := SignedDifference.sign_iff p.bits n.bits
  cases hs : SignedDifference.sign p.bits n.bits <;> simp_all

private theorem shifted_represents (bs : List Bool) (origin : ℤ) :
    (BitTape.shifted bs origin).Represents bs := by
  intro k
  simp [BitTape.shifted]

theorem emitPair_numerator_length_le (v : ℕ → ℕ) (hd : 0 < v 32) :
    (emitPair v hd).numerator.natAbs.bits.length ≤
      max (v 30).bits.length (v 31).bits.length + 1 := by
  have hlen := canonical_length_le (SignedDifference.magnitude (v 30).bits (v 31).bits)
  have hmag := SignedDifference.magnitude_length_le (v 30).bits (v 31).bits
  dsimp [emitPair]
  rw [← magnitude_eq_natAbs]
  omega

/-- Emit the exact raw rational pair. Copies of the numerator magnitude and
denominator remain at their end positions on scratch tapes 2 and 3. -/
theorem emit_bank_with_operands (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (hd : 0 < v 32) (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store, ∃ numOrigin denOrigin : ℤ,
      cost ≤ 300 * ((v 30).bits.length + (v 31).bits.length + (v 32).bits.length + 4) ∧
      Executes input tape emitCode cost s t ∧
      t.val.output = (emitPair v hd).encode.reverse ++ s.val.output ∧
      Bank t.val v ∧
      t.val.tapes 2 = BitTape.shiftedEnd (emitPair v hd).numerator.natAbs.bits numOrigin ∧
      t.val.tapes 3 = BitTape.shiftedEnd (v 32).bits denOrigin ∧ EmitFrame s.val t.val ∧
      EmitOperands t.val (v 30) (v 31) := by
  obtain ⟨ao, h0⟩ := hready.1
  obtain ⟨xo, h1⟩ := (zero_word_iff_blank s.val 1).mp hready.2.1
  obtain ⟨zo, h2⟩ := hready.2.2.1
  obtain ⟨yo, h3⟩ := hready.2.2.2
  obtain ⟨po, h30⟩ := hbank 30 (by omega) (by omega)
  obtain ⟨qo, h31⟩ := hbank 31 (by omega) (by omega)
  obtain ⟨ro, h32⟩ := hbank 32 (by omega) (by omega)
  obtain ⟨a, hea, ha0, hat, hao, haf⟩ := clone_scratch 30 0 (by omega) (by omega)
    input tape (v 30) po ao s h30 h0
  obtain ⟨b, heb, hb1, hbt, hbo, hbf⟩ := clone_scratch 31 1 (by omega) (by omega)
    input tape (v 31) qo xo a ((hat 31 (by omega)).trans h31) ((hat 1 (by omega)).trans h1)
  obtain ⟨c, hec, hc3, hct, hco, hcf⟩ := clone_scratch 32 3 (by omega) (by omega)
    input tape (v 32) ro yo b
    ((hbt 32 (by omega)).trans ((hat 32 (by omega)).trans h32))
    ((hbt 3 (by omega)).trans ((hat 3 (by omega)).trans h3))
  have hc0 := (hct 0 (by omega)).trans ((hbt 0 (by omega)).trans ha0)
  have hc1 := (hct 1 (by omega)).trans hb1
  have hc2 := (hct 2 (by omega)).trans ((hbt 2 (by omega)).trans ((hat 2 (by omega)).trans h2))
  obtain ⟨diffCost, diff, origin, hdCost, hed, hdp, hsign, hd2, hd0, hd1⟩ :=
    SignedDifference.simulation_cleanup input tape c.val (v 30).bits (v 31).bits ao xo zo
      c.property hc0 hc1 hc2
  have hdf := SignedDifference.execution_frame input tape hed
  let d : Store := Store.ofState diff
  have hed' : Executes input tape (.call SignedDifference.program) (diffCost + 1) c d :=
    Executes.call _ _ _ _ hed (by
      simp [SignedDifference.program, hdp, SignedDifference.padProgram,
        Subtraction.program, Subtraction.swappedProgram, BitRAM.renameTapes,
        RewindOvershoot.program, RewindOvershoot.preamble, Rewind.program,
        BitRAM.link, TapeOps.clear, TapeOps.trim, BitRAMInstruction.relocate])
  let num := (emitPair v hd).numerator.natAbs.bits
  have hd2' : d.val.tapes 2 = BitTape.shiftedEnd num origin := by
    simpa [d, Store.ofState, num, emitPair, magnitude_eq_natAbs] using hd2
  have hr := WordTransfer.rewind_shifted 2 origin input tape num d.val d.property hd2'
  let r : Store := Store.ofState (Rewind.finishAt 2 origin d.val)
  have her : Executes input tape (.call (Rewind.program 2)) (4 * num.length + 6) d r :=
    Executes.call _ _ _ _ hr.1 (by simp [Rewind.program, Rewind.finishAt])
  have hr2 : r.val.tapes 2 = BitTape.shifted num origin := hr.2
  have hr3 : r.val.tapes 3 = BitTape.shifted (v 32).bits yo := by
    have hh := (hdf.2.2.2.2.2.1 3 (by omega)).trans hc3
    simpa [r, d, Store.ofState, Rewind.finishAt] using hh
  have hrSign : r.val.registers 23 = decide ((emitPair v hd).numerator < 0) := by
    simpa [r, d, Store.ofState, Rewind.finishAt, emitPair, difference_sign] using hsign
  have he := EmitRat.steps 2 3 (by omega) input tape num (v 32).bits r.val r.property
    (by rw [hr2]; exact shifted_represents _ _)
    (by rw [hr3]; exact shifted_represents _ _)
    (by rw [hr2]; simp [BitTape.shifted])
    (by rw [hr3]; simp [BitTape.shifted])
  let t : Store := Store.ofState (EmitRat.finish 2 3 num (v 32).bits r.val)
  have he' : Executes input tape (.call (EmitRat.program 2 3))
      (16 * (num.length + (v 32).bits.length) + 38) r t :=
    Executes.call _ _ _ _ he (by
      simp [EmitRat.finish, EmitRat.program, EmitNat.program, TapeIO.program,
        Rewind.program, BitRAMInstruction.relocate])
  have hrf : EmitFrame d.val r.val := rewind_frame origin d.val
  have hef : EmitFrame r.val t.val := emit_frame num (v 32).bits r.val
  have hf : EmitFrame s.val t.val :=
    ((((haf.trans hbf).trans hcf).trans (difference_frame hdf)).trans hrf).trans hef
  refine ⟨(15 * (v 30).bits.length + 17) + ((15 * (v 31).bits.length + 17) +
    ((15 * (v 32).bits.length + 17) + ((diffCost + 1) +
      ((4 * num.length + 6) + (16 * (num.length + (v 32).bits.length) + 38))))),
    t, origin, yo, ?_, hea.seq (heb.seq (hec.seq (hed'.seq (her.seq he')))), ?_, ?_, ?_, ?_, hf, ?_⟩
  · have hnum : num.length ≤ max (v 30).bits.length (v 31).bits.length + 1 :=
      emitPair_numerator_length_le v hd
    omega
  · have ho := EmitRat.finish_pair_output 2 3 (emitPair v hd) r.val hrSign
    have hro : r.val.output = s.val.output :=
      hdf.2.2.2.2.1.trans (hco.trans (hbo.trans hao))
    simpa [t, Store.ofState, num, emitPair, hro] using ho
  · intro i hi hi'
    exact word_of_eq (hf.2.2.2.2.1 i (by omega)) (hbank i hi hi')
  · have ht2 : t.val.tapes 2 = {r.val.tapes 2 with head := (r.val.tapes 2).head + num.length} := by
      simp [t, Store.ofState, EmitRat.finish, EmitRat.denominatorStart,
        EmitNat.finish, EmitNat.payloadStart, EmitNat.rewindStart, EmitNat.separatorStart,
        EmitNat.headerStart, TapeIO.finish, Rewind.finishAt, EmitRat.numeratorStart]
    rw [hr2] at ht2
    exact ht2
  · have ht3 : t.val.tapes 3 =
        {r.val.tapes 3 with head := (r.val.tapes 3).head + (v 32).bits.length} := by
      simp [t, Store.ofState, EmitRat.finish, EmitRat.denominatorStart,
        EmitNat.finish, EmitNat.payloadStart, EmitNat.rewindStart, EmitNat.separatorStart,
        EmitNat.headerStart, TapeIO.finish, Rewind.finishAt, EmitRat.numeratorStart]
    rw [hr3] at ht3
    exact ht3
  · refine ⟨ao, xo, ?_, ?_⟩
    · simpa [t, r, d, Store.ofState, EmitRat.finish, EmitRat.denominatorStart,
        EmitNat.finish, EmitNat.payloadStart, EmitNat.rewindStart, EmitNat.separatorStart,
        EmitNat.headerStart, TapeIO.finish, Rewind.finishAt, EmitRat.numeratorStart] using hd0
    · simpa [t, r, d, Store.ofState, EmitRat.finish, EmitRat.denominatorStart,
        EmitNat.finish, EmitNat.payloadStart, EmitNat.rewindStart, EmitNat.separatorStart,
        EmitNat.headerStart, TapeIO.finish, Rewind.finishAt, EmitRat.numeratorStart] using hd1

theorem emit_bank (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (hd : 0 < v 32) (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store, ∃ numOrigin denOrigin : ℤ,
      cost ≤ 300 * ((v 30).bits.length + (v 31).bits.length + (v 32).bits.length + 4) ∧
      Executes input tape emitCode cost s t ∧
      t.val.output = (emitPair v hd).encode.reverse ++ s.val.output ∧
      Bank t.val v ∧
      t.val.tapes 2 = BitTape.shiftedEnd (emitPair v hd).numerator.natAbs.bits numOrigin ∧
      t.val.tapes 3 = BitTape.shiftedEnd (v 32).bits denOrigin ∧ EmitFrame s.val t.val := by
  obtain ⟨cost, t, no, den, hc, he, ho, hb, hn, hd', hf, _⟩ :=
    emit_bank_with_operands input tape v hd s hbank hready
  exact ⟨cost, t, no, den, hc, he, ho, hb, hn, hd', hf⟩

theorem emit_compiled_run (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (hd : 0 < v 32) (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ t : Store, ∃ numOrigin denOrigin : ℤ,
      (runPriced (emitCode.compile.next input tape)
        (300 * ((v 30).bits.length + (v 31).bits.length + (v 32).bits.length + 4) + 1)
        s.val).finished = some (t.place emitCode.size) ∧
      (runPriced (emitCode.compile.next input tape)
        (300 * ((v 30).bits.length + (v 31).bits.length + (v 32).bits.length + 4) + 1)
        s.val).instructions ≤
        300 * ((v 30).bits.length + (v 31).bits.length + (v 32).bits.length + 4) ∧
      t.val.output = (emitPair v hd).encode.reverse ++ s.val.output ∧
      Bank t.val v ∧
      t.val.tapes 2 = BitTape.shiftedEnd (emitPair v hd).numerator.natAbs.bits numOrigin ∧
      t.val.tapes 3 = BitTape.shiftedEnd (v 32).bits denOrigin ∧ EmitFrame s.val t.val := by
  obtain ⟨cost, t, no, den, hc, he, ho, hb, hn, hd', hf⟩ :=
    emit_bank input tape v hd s hbank hready
  have hr := he.compiled_run
    (300 * ((v 30).bits.length + (v 31).bits.length + (v 32).bits.length + 4) + 1) (by omega)
  exact ⟨t, no, den, hr.1, hr.2 ▸ hc, ho, hb, hn, hd', hf⟩

end Maxwell.Cost.RationalAccumulator
