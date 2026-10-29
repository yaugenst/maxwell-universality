import Maxwell.Cost.RationalAccumulator.Emit

namespace Maxwell.Cost.RationalAccumulator

open Structured

def eraseEndCode (workTape : ℕ) : Code :=
  .seq (.call (Rewind.program workTape)) (.call (TapeOps.clear workTape))

def eraseOvershootCode (workTape : ℕ) : Code :=
  .seq (.call (RewindOvershoot.program workTape)) (.call (TapeOps.clear workTape))

theorem erase_end (workTape : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (bits : List Bool) (origin : ℤ) (s : Store)
    (hw : s.val.tapes workTape = BitTape.shiftedEnd bits origin) :
    ∃ t : Store, Executes input tape (eraseEndCode workTape) (10 * bits.length + 10) s t ∧
      Blank t.val workTape ∧ WordTransfer.Frame workTape workTape s.val t.val := by
  have hr := WordTransfer.rewind_shifted workTape origin input tape bits s.val s.property hw
  let r : Store := Store.ofState (Rewind.finishAt workTape origin s.val)
  have her : Executes input tape (.call (Rewind.program workTape)) (4 * bits.length + 6) s r :=
    Executes.call _ _ _ _ hr.1 (by simp [Rewind.program, Rewind.finishAt])
  obtain ⟨t, ht, hp, hblank, hf⟩ := TapeOps.clear_steps workTape input tape bits origin
    r.val r.property hr.2
  have het : Executes input tape (.call (TapeOps.clear workTape))
      (6 * bits.length + 4) r (Store.ofState t) :=
    Executes.call _ _ _ _ ht (by simp [TapeOps.clear, hp])
  refine ⟨Store.ofState t, ?_, ⟨origin + bits.length, hblank⟩,
    (WordTransfer.frame_rewind workTape workTape workTape (Or.inl rfl) origin s.val).trans
      (WordTransfer.frame_of_copy hf)⟩
  convert her.seq het using 1 <;> first | rfl | omega

theorem erase_overshoot (workTape : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (bits : List Bool) (origin : ℤ) (distance : ℕ) (hbits : 0 < bits.length)
    (hdistance : bits.length ≤ distance) (s : Store)
    (hw : s.val.tapes workTape = {BitTape.shifted bits origin with head := origin + distance}) :
    ∃ t : Store, Executes input tape (eraseOvershootCode workTape)
        (4 * distance + 6 * bits.length + 11) s t ∧
      Blank t.val workTape ∧ WordTransfer.Frame workTape workTape s.val t.val := by
  have hr := WordTransfer.rewind_overshoot_shifted workTape origin input tape bits distance
    hbits hdistance s.val s.property hw
  let r : Store := Store.ofState (RewindOvershoot.finish workTape origin s.val)
  have her : Executes input tape (.call (RewindOvershoot.program workTape))
      (4 * distance + 7) s r :=
    Executes.call _ _ _ _ hr.1 (by
      simp [RewindOvershoot.program, RewindOvershoot.preamble, RewindOvershoot.finish,
        BitRAM.link, Rewind.program, Rewind.finishAt])
  obtain ⟨t, ht, hp, hblank, hf⟩ := TapeOps.clear_steps workTape input tape bits origin
    r.val r.property hr.2
  have het : Executes input tape (.call (TapeOps.clear workTape))
      (6 * bits.length + 4) r (Store.ofState t) :=
    Executes.call _ _ _ _ ht (by simp [TapeOps.clear, hp])
  refine ⟨Store.ofState t, ?_, ⟨origin + bits.length, hblank⟩,
    (WordTransfer.frame_rewind workTape workTape workTape (Or.inl rfl) origin s.val).trans
      (WordTransfer.frame_of_copy hf)⟩
  convert her.seq het using 1 <;> first | rfl | omega

def emitCleanupCode : Code :=
  .seq (eraseOvershootCode 0)
    (.seq (eraseOvershootCode 1) (.seq (eraseEndCode 2) (eraseEndCode 3)))

private theorem erase_frame {workTape : ℕ} (hw : workTape < 4) {s t : BitRAMState}
    (h : WordTransfer.Frame workTape workTape s t) : EmitFrame s t := by
  rcases h with ⟨ha, hi, hm, hr, _, ht, hg⟩
  exact ⟨ha, hi, hm, hr, fun i h4 => ht i (by omega) (by omega),
    fun i _ _ h24 h25 h26 h27 _ => hg i h24 h25 h26 h27⟩

theorem cleanup_emitted (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (hd : 0 < v 32) (s : Store) (no den : ℤ) (hbank : Bank s.val v)
    (hop : EmitOperands s.val (v 30) (v 31))
    (hn : s.val.tapes 2 = BitTape.shiftedEnd (emitPair v hd).numerator.natAbs.bits no)
    (hdn : s.val.tapes 3 = BitTape.shiftedEnd (v 32).bits den) :
    ∃ cost, ∃ t : Store,
      cost ≤ 100 * ((v 30).bits.length + (v 31).bits.length + (v 32).bits.length + 4) ∧
      Executes input tape emitCleanupCode cost s t ∧
      Bank t.val v ∧ Scratch t.val 0 ∧ t.val.output = s.val.output ∧ EmitFrame s.val t.val := by
  obtain ⟨po, qo, hp, hq⟩ := hop
  let ps := SignedDifference.padded (v 30).bits
  let qs := SignedDifference.padded (v 31).bits
  let distance := max ps.length qs.length
  obtain ⟨a, hea, ha, haf⟩ := erase_overshoot 0 input tape ps po distance
    (SignedDifference.padded_pos _) (le_max_left _ _) s hp
  obtain ⟨b, heb, hb, hbf⟩ := erase_overshoot 1 input tape qs qo distance
    (SignedDifference.padded_pos _) (le_max_right _ _) a
    ((haf.2.2.2.2.2.1 1 (by omega) (by omega)).trans hq)
  obtain ⟨c, hec, hc, hcf⟩ := erase_end 2 input tape (emitPair v hd).numerator.natAbs.bits no b
    ((hbf.2.2.2.2.2.1 2 (by omega) (by omega)).trans
      ((haf.2.2.2.2.2.1 2 (by omega) (by omega)).trans hn))
  obtain ⟨t, het, ht, htf⟩ := erase_end 3 input tape (v 32).bits den c
    ((hcf.2.2.2.2.2.1 3 (by omega) (by omega)).trans
      ((hbf.2.2.2.2.2.1 3 (by omega) (by omega)).trans
        ((haf.2.2.2.2.2.1 3 (by omega) (by omega)).trans hdn)))
  have hf : EmitFrame s.val t.val :=
    (((erase_frame (by omega) haf).trans (erase_frame (by omega) hbf)).trans
      (erase_frame (by omega) hcf)).trans (erase_frame (by omega) htf)
  refine ⟨(4 * distance + 6 * ps.length + 11) + ((4 * distance + 6 * qs.length + 11) +
      ((10 * (emitPair v hd).numerator.natAbs.bits.length + 10) +
        (10 * (v 32).bits.length + 10))), t, ?_, hea.seq (heb.seq (hec.seq het)), ?_, ?_,
    htf.2.2.2.2.1.trans (hcf.2.2.2.2.1.trans (hbf.2.2.2.2.1.trans haf.2.2.2.2.1)), hf⟩
  · have hpLength := SignedDifference.padded_length (v 30).bits
    have hqLength := SignedDifference.padded_length (v 31).bits
    have hnLength := emitPair_numerator_length_le v hd
    dsimp [distance, ps, qs]
    omega
  · intro i hi hi'
    exact word_of_eq (hf.2.2.2.2.1 i (by omega)) (hbank i hi hi')
  · refine ⟨blank_of_eq ((htf.2.2.2.2.2.1 0 (by omega) (by omega)).trans
        ((hcf.2.2.2.2.2.1 0 (by omega) (by omega)).trans
          (hbf.2.2.2.2.2.1 0 (by omega) (by omega)))) ha,
      (zero_word_iff_blank _ _).mpr (blank_of_eq
        ((htf.2.2.2.2.2.1 1 (by omega) (by omega)).trans
          (hcf.2.2.2.2.2.1 1 (by omega) (by omega))) hb),
      blank_of_eq (htf.2.2.2.2.2.1 2 (by omega) (by omega)) hc, ht⟩

/-- A complete row endpoint, including every rewind and scratch erasure. -/
def emitCleanCode : Code := .seq emitCode emitCleanupCode

theorem emit_clean_bank (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (hd : 0 < v 32) (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store,
      cost ≤ 400 * ((v 30).bits.length + (v 31).bits.length + (v 32).bits.length + 4) ∧
      Executes input tape emitCleanCode cost s t ∧
      t.val.output = (emitPair v hd).encode.reverse ++ s.val.output ∧
      Bank t.val v ∧ Scratch t.val 0 ∧ EmitFrame s.val t.val := by
  obtain ⟨emitCost, a, no, den, heCost, he, ho, hb, hn, hd', hef, hop⟩ :=
    emit_bank_with_operands input tape v hd s hbank hready
  obtain ⟨cleanCost, t, hcCost, hc, hbt, hs, hco, hcf⟩ :=
    cleanup_emitted input tape v hd a no den hb hop hn hd'
  exact ⟨emitCost + cleanCost, t, by omega, he.seq hc, hco.trans ho, hbt, hs, hef.trans hcf⟩

theorem emit_clean_compiled_run (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (hd : 0 < v 32) (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ t : Store,
      (runPriced (emitCleanCode.compile.next input tape)
        (400 * ((v 30).bits.length + (v 31).bits.length + (v 32).bits.length + 4) + 1)
        s.val).finished = some (t.place emitCleanCode.size) ∧
      (runPriced (emitCleanCode.compile.next input tape)
        (400 * ((v 30).bits.length + (v 31).bits.length + (v 32).bits.length + 4) + 1)
        s.val).instructions ≤
        400 * ((v 30).bits.length + (v 31).bits.length + (v 32).bits.length + 4) ∧
      t.val.output = (emitPair v hd).encode.reverse ++ s.val.output ∧
      Bank t.val v ∧ Scratch t.val 0 ∧ EmitFrame s.val t.val := by
  obtain ⟨cost, t, hc, he, ho, hb, hs, hf⟩ := emit_clean_bank input tape v hd s hbank hready
  have hr := he.compiled_run
    (400 * ((v 30).bits.length + (v 31).bits.length + (v 32).bits.length + 4) + 1) (by omega)
  exact ⟨t, hr.1, hr.2 ▸ hc, ho, hb, hs, hf⟩

end Maxwell.Cost.RationalAccumulator
