import Maxwell.Cost.RationalAccumulator.EmitCleanup
import Maxwell.Cost.Structured.Primitive

namespace Maxwell.Cost.RationalCompare

open Structured RationalAccumulator

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → (i < 30 ∨ 36 < i) → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 23 → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 35 →
    t.registers i = s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i h4 hb => (kt i h4 hb).trans (ht i h4 hb),
    fun i h15 h23 h24 h25 h26 h27 h35 =>
      (kg i h15 h23 h24 h25 h26 h27 h35).trans (hg i h15 h23 h24 h25 h26 h27 h35)⟩

theorem frame_of_bank {s t : BitRAMState} (h : RationalAccumulator.Frame s t) : Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, ht, fun i hi _ h24 h25 h26 h27 _ => hg i hi h24 h25 h26 h27⟩

private theorem difference_frame {s t : BitRAMState} (h : SignedDifference.Frame s t) : Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i hi _ => ht i (by omega),
    fun i hi h23 h24 h25 h26 h27 _ => hg i hi h23 h24 h25 h26 h27⟩

private theorem transfer_frame {source target : ℕ} {s t : BitRAMState}
    (hs : source < 4 ∨ (30 ≤ source ∧ source ≤ 36))
    (ht : target < 4 ∨ (30 ≤ target ∧ target ≤ 36))
    (h : WordTransfer.Frame source target s t) : Frame s t :=
  frame_of_bank (clone_frame hs ht h)

def cleared (v : ℕ → ℕ) : ℕ → ℕ := Function.update (Function.update v 36 0) 35 0

def temporaryCode : Code :=
  .seq (.call (WordTransfer.move 36 0))
    (.seq (.call (WordTransfer.move 35 1))
      (.seq (.call SignedDifference.program)
        (.seq (eraseOvershootCode 0)
          (.seq (eraseOvershootCode 1)
            (.seq (eraseEndCode 2) (Code.atom (.bitAnd 35 23 23)))))))

private theorem canonical_length_le (bs : List Bool) : (addressValue bs).bits.length ≤ bs.length := by
  obtain ⟨core, n, hbs, hc⟩ := TapeOps.trailing_zero_decomposition bs
  rw [hbs, TapeOps.addressValue_append_zeros, TapeOps.canonicalBits_bits hc]
  simp

/-- Compare the two stored cross-products, move their temporary words out of
the bank, and erase every arithmetic scratch word before returning. -/
theorem compare_temporaries (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store,
      cost ≤ 300 * ((v 35).bits.length + (v 36).bits.length + 4) ∧
      Executes input tape temporaryCode cost s t ∧
      t.val.registers 35 = decide (v 36 < v 35) ∧
      Bank t.val (cleared v) ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨ao, h0⟩ := hready.1
  obtain ⟨xo, h1⟩ := (zero_word_iff_blank s.val 1).mp hready.2.1
  obtain ⟨zo, h2⟩ := hready.2.2.1
  obtain ⟨yo, h3⟩ := hready.2.2.2
  obtain ⟨po, h36⟩ := hbank 36 (by omega) (by omega)
  obtain ⟨qo, h35⟩ := hbank 35 (by omega) (by omega)
  obtain ⟨movedA, hma, hmap, hma36, hma0, hmaf⟩ := WordTransfer.move_steps 36 0 (by omega)
    input tape (v 36).bits po ao s.val s.property h36 h0
  let a : Store := Store.ofState movedA
  have hea : Executes input tape (.call (WordTransfer.move 36 0))
      (12 * (v 36).bits.length + 11) s a :=
    Executes.call _ _ _ _ hma (by
      simp [WordTransfer.move, hmap, TapeOps.copyClear, Rewind.program, BitRAMInstruction.relocate])
  obtain ⟨movedB, hmb, hmbp, hmb35, hmb1, hmbf⟩ := WordTransfer.move_steps 35 1 (by omega)
    input tape (v 35).bits qo xo a.val a.property
    ((hmaf.2.2.2.2.2.1 35 (by omega) (by omega)).trans h35)
    ((hmaf.2.2.2.2.2.1 1 (by omega) (by omega)).trans h1)
  let b : Store := Store.ofState movedB
  have heb : Executes input tape (.call (WordTransfer.move 35 1))
      (12 * (v 35).bits.length + 11) a b :=
    Executes.call _ _ _ _ hmb (by
      simp [WordTransfer.move, hmbp, TapeOps.copyClear, Rewind.program, BitRAMInstruction.relocate])
  have hbb : Bank b.val (cleared v) := by
    intro i hi hi'
    by_cases hi35 : i = 35
    · subst i
      simp only [cleared, Function.update_self, zero_word_iff_blank]
      exact ⟨qo + (v 35).bits.length, hmb35⟩
    · by_cases hi36 : i = 36
      · subst i
        simp only [cleared, Function.update_of_ne (show 36 ≠ 35 by omega),
          Function.update_self, zero_word_iff_blank]
        exact ⟨po + (v 36).bits.length, (hmbf.2.2.2.2.2.1 36 (by omega) (by omega)).trans hma36⟩
      · simp only [cleared, Function.update_of_ne hi35, Function.update_of_ne hi36]
        exact word_of_eq ((hmbf.2.2.2.2.2.1 i hi35 (by omega)).trans
          (hmaf.2.2.2.2.2.1 i hi36 (by omega))) (hbank i hi hi')
  have hb0 := (hmbf.2.2.2.2.2.1 0 (by omega) (by omega)).trans hma0
  have hb2 := (hmbf.2.2.2.2.2.1 2 (by omega) (by omega)).trans
    ((hmaf.2.2.2.2.2.1 2 (by omega) (by omega)).trans h2)
  have hb3 := (hmbf.2.2.2.2.2.1 3 (by omega) (by omega)).trans
    ((hmaf.2.2.2.2.2.1 3 (by omega) (by omega)).trans h3)
  obtain ⟨diffCost, diff, origin, hdCost, hed, hdp, hdSign, hd2, hd0, hd1⟩ :=
    SignedDifference.simulation_cleanup input tape b.val (v 36).bits (v 35).bits ao xo zo
      b.property hb0 hmb1 hb2
  have hdf := SignedDifference.execution_frame input tape hed
  let d : Store := Store.ofState diff
  have hed' : Executes input tape (.call SignedDifference.program) (diffCost + 1) b d :=
    Executes.call _ _ _ _ hed (by
      simp [SignedDifference.program, hdp, SignedDifference.padProgram, Subtraction.program,
        Subtraction.swappedProgram, BitRAM.renameTapes, RewindOvershoot.program,
        RewindOvershoot.preamble, Rewind.program, BitRAM.link, TapeOps.clear, TapeOps.trim,
        BitRAMInstruction.relocate])
  let ps := SignedDifference.padded (v 36).bits
  let qs := SignedDifference.padded (v 35).bits
  let distance := max ps.length qs.length
  let num := (addressValue (SignedDifference.magnitude (v 36).bits (v 35).bits)).bits
  obtain ⟨e, hee, he0, hef⟩ := erase_overshoot 0 input tape ps ao distance
    (SignedDifference.padded_pos _) (le_max_left _ _) d hd0
  obtain ⟨f, hef', hf1, hff⟩ := erase_overshoot 1 input tape qs xo distance
    (SignedDifference.padded_pos _) (le_max_right _ _) e
    ((hef.2.2.2.2.2.1 1 (by omega) (by omega)).trans hd1)
  obtain ⟨g, heg, hg2, hgf⟩ := erase_end 2 input tape num origin f
    ((hff.2.2.2.2.2.1 2 (by omega) (by omega)).trans
      ((hef.2.2.2.2.2.1 2 (by omega) (by omega)).trans hd2))
  let t : Store := Store.ofState (g.val.setRegister 35 (g.val.registers 23 && g.val.registers 23))
  have het : Executes input tape (Code.atom (.bitAnd 35 23 23)) 2 g t :=
    Executes.bitAnd input tape g 35 23 23
  have htFrame : Frame g.val t.val := by
    simp [t, Store.ofState, Frame, BitRAMState.setRegister]
    intro i _ _ _ _ _ _ h35
    simp [h35]
  have hfg : Frame s.val g.val :=
    (((((transfer_frame (Or.inr (by omega)) (Or.inl (by omega)) hmaf).trans
      (transfer_frame (Or.inr (by omega)) (Or.inl (by omega)) hmbf)).trans
      (difference_frame hdf)).trans
      (transfer_frame (Or.inl (by omega)) (Or.inl (by omega)) hef)).trans
      (transfer_frame (Or.inl (by omega)) (Or.inl (by omega)) hff)).trans
      (transfer_frame (Or.inl (by omega)) (Or.inl (by omega)) hgf)
  refine ⟨(12 * (v 36).bits.length + 11) + ((12 * (v 35).bits.length + 11) +
      ((diffCost + 1) + ((4 * distance + 6 * ps.length + 11) +
      ((4 * distance + 6 * qs.length + 11) + ((10 * num.length + 10) + 2))))),
    t, ?_, hea.seq (heb.seq (hed'.seq (hee.seq (hef'.seq (heg.seq het))))), ?_, ?_, ?_,
    hfg.trans htFrame⟩
  · have hpLength := SignedDifference.padded_length (v 36).bits
    have hqLength := SignedDifference.padded_length (v 35).bits
    have hnLength := canonical_length_le (SignedDifference.magnitude (v 36).bits (v 35).bits)
    have hmLength := SignedDifference.magnitude_length_le (v 36).bits (v 35).bits
    dsimp [distance, ps, qs, num]
    omega
  · have hgs : g.val.registers 23 = SignedDifference.sign (v 36).bits (v 35).bits :=
      (hgf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega)).trans
        ((hff.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega)).trans
          ((hef.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega)).trans hdSign))
    have hs := SignedDifference.sign_iff (v 36).bits (v 35).bits
    simp only [address_bits] at hs
    simp only [t, Store.ofState, BitRAMState.setRegister, Function.update_self, Bool.and_self, hgs]
    cases hh : SignedDifference.sign (v 36).bits (v 35).bits <;> simp_all
  · intro i hi hi'
    exact word_of_eq ((hgf.2.2.2.2.2.1 i (by omega) (by omega)).trans
      ((hff.2.2.2.2.2.1 i (by omega) (by omega)).trans
        ((hef.2.2.2.2.2.1 i (by omega) (by omega)).trans
          (hdf.2.2.2.2.2.1 i (by omega))))) (hbb i hi hi')
  · refine ⟨blank_of_eq ((hgf.2.2.2.2.2.1 0 (by omega) (by omega)).trans
        (hff.2.2.2.2.2.1 0 (by omega) (by omega))) he0,
      (zero_word_iff_blank _ _).mpr (blank_of_eq
        (hgf.2.2.2.2.2.1 1 (by omega) (by omega)) hf1), hg2, ⟨yo, ?_⟩⟩
    exact (hgf.2.2.2.2.2.1 3 (by omega) (by omega)).trans
      ((hff.2.2.2.2.2.1 3 (by omega) (by omega)).trans
        ((hef.2.2.2.2.2.1 3 (by omega) (by omega)).trans
          ((hdf.2.2.2.2.2.1 3 (by omega)).trans hb3)))

end Maxwell.Cost.RationalCompare
