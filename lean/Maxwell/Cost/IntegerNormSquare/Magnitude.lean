import Maxwell.Cost.DyadicSqrt.Bank

namespace Maxwell.Cost.IntegerNormSquare

open Structured RationalAccumulator

def magnitude (a b : ℕ) : ℕ := ((a : ℤ) - b).natAbs

theorem magnitude_eq (a b : ℕ) :
    addressValue (SignedDifference.magnitude a.bits b.bits) = magnitude a b := by
  have h := congrArg Int.natAbs (SignedDifference.signed_value a.bits b.bits)
  cases hs : SignedDifference.sign a.bits b.bits <;> simpa [hs, magnitude] using h

theorem magnitude_bits_length_le (a b : ℕ) :
    (magnitude a b).bits.length ≤ max a.bits.length b.bits.length + 1 := by
  have hc : ∀ bs : List Bool, (addressValue bs).bits.length ≤ bs.length := by
    intro bs
    obtain ⟨core, n, hbs, hcore⟩ := TapeOps.trailing_zero_decomposition bs
    rw [hbs, TapeOps.addressValue_append_zeros, TapeOps.canonicalBits_bits hcore]
    simp
  rw [← magnitude_eq]
  exact (hc _).trans (SignedDifference.magnitude_length_le _ _)

private theorem difference_frame {s t : BitRAMState} (h : SignedDifference.Frame s t) :
    DyadicSqrt.Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i hi _ => ht i (by omega),
    fun i hi h23 h24 h25 h26 h27 _ => hg i hi h23 h24 h25 h26 h27⟩

private theorem transfer_frame {source target : ℕ} {s t : BitRAMState}
    (hs : source < 4 ∨ (30 ≤ source ∧ source ≤ 36))
    (ht : target < 4 ∨ (30 ≤ target ∧ target ≤ 36))
    (h : WordTransfer.Frame source target s t) : DyadicSqrt.Frame s t :=
  DyadicSqrt.frame_of_bank (clone_frame hs ht h)

def magnitudeCode : Code :=
  .seq (.call (WordTransfer.clone 30 0))
    (.seq (.call (WordTransfer.clone 31 1))
      (.seq (.call SignedDifference.program)
        (.seq (eraseOvershootCode 0)
          (.seq (eraseOvershootCode 1)
            (.seq (.call (Rewind.program 2)) (.call (WordTransfer.move 2 34)))))))

/-- Copy the signed channels, compute their canonical absolute difference,
and move it into the bank while restoring every arithmetic scratch tape. -/
theorem store_magnitude_signed (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) (hzero : v 34 = 0) :
    ∃ cost, ∃ t : Store,
      cost ≤ 300 * ((v 30).bits.length + (v 31).bits.length + 4) ∧
      Executes input tape magnitudeCode cost s t ∧
      Bank t.val (Function.update v 34 (magnitude (v 30) (v 31))) ∧
      Scratch t.val 0 ∧ DyadicSqrt.Frame s.val t.val ∧
      t.val.registers 23 = SignedDifference.sign (v 30).bits (v 31).bits := by
  obtain ⟨ao, h0⟩ := hready.1
  obtain ⟨xo, h1⟩ := (zero_word_iff_blank s.val 1).mp hready.2.1
  obtain ⟨zo, h2⟩ := hready.2.2.1
  obtain ⟨yo, h3⟩ := hready.2.2.2
  obtain ⟨po, h30⟩ := hbank 30 (by omega) (by omega)
  obtain ⟨qo, h31⟩ := hbank 31 (by omega) (by omega)
  have hb34 := hbank 34 (by omega) (by omega)
  rw [hzero, zero_word_iff_blank] at hb34
  obtain ⟨outOrigin, h34⟩ := hb34
  obtain ⟨copiedA, hca, hcap, hca30, hca0, hcaf⟩ := WordTransfer.clone_steps 30 0
    (by omega) input tape (v 30).bits po ao s.val s.property h30 h0
  let a : Store := Store.ofState copiedA
  have hea : Executes input tape (.call (WordTransfer.clone 30 0))
      (15 * (v 30).bits.length + 17) s a :=
    Executes.call _ _ _ _ hca (by
      simp [WordTransfer.clone, hcap, Copy.program, Rewind.program, BitRAMInstruction.relocate])
  have hat (i : ℕ) (hi : i ≠ 0) : a.val.tapes i = s.val.tapes i := by
    by_cases h : i = 30
    · subst i; exact hca30.trans h30.symm
    · exact hcaf.2.2.2.2.2.1 i h hi
  obtain ⟨copiedB, hcb, hcbp, hcb31, hcb1, hcbf⟩ := WordTransfer.clone_steps 31 1
    (by omega) input tape (v 31).bits qo xo a.val a.property
    ((hat 31 (by omega)).trans h31) ((hat 1 (by omega)).trans h1)
  let b : Store := Store.ofState copiedB
  have heb : Executes input tape (.call (WordTransfer.clone 31 1))
      (15 * (v 31).bits.length + 17) a b :=
    Executes.call _ _ _ _ hcb (by
      simp [WordTransfer.clone, hcbp, Copy.program, Rewind.program, BitRAMInstruction.relocate])
  have hbt (i : ℕ) (hi : i ≠ 1) : b.val.tapes i = a.val.tapes i := by
    by_cases h : i = 31
    · subst i; exact hcb31.trans ((hat 31 (by omega)).trans h31).symm
    · exact hcbf.2.2.2.2.2.1 i h hi
  obtain ⟨diffCost, diff, origin, hdCost, hed, hdp, hdSign, hd2, hd0, hd1⟩ :=
    SignedDifference.simulation_cleanup input tape b.val (v 30).bits (v 31).bits ao xo zo
      b.property ((hbt 0 (by omega)).trans hca0) hcb1
      ((hbt 2 (by omega)).trans ((hat 2 (by omega)).trans h2))
  have hdf := SignedDifference.execution_frame input tape hed
  let d : Store := Store.ofState diff
  have hed' : Executes input tape (.call SignedDifference.program) (diffCost + 1) b d :=
    Executes.call _ _ _ _ hed (by
      simp [SignedDifference.program, hdp, SignedDifference.padProgram, Subtraction.program,
        Subtraction.swappedProgram, BitRAM.renameTapes, RewindOvershoot.program,
        RewindOvershoot.preamble, Rewind.program, BitRAM.link, TapeOps.clear, TapeOps.trim,
        BitRAMInstruction.relocate])
  let ps := SignedDifference.padded (v 30).bits
  let qs := SignedDifference.padded (v 31).bits
  let distance := max ps.length qs.length
  let num := (magnitude (v 30) (v 31)).bits
  obtain ⟨e, hee, he0, hef⟩ := erase_overshoot 0 input tape ps ao distance
    (SignedDifference.padded_pos _) (le_max_left _ _) d hd0
  obtain ⟨f, hef', hf1, hff⟩ := erase_overshoot 1 input tape qs xo distance
    (SignedDifference.padded_pos _) (le_max_right _ _) e
    ((hef.2.2.2.2.2.1 1 (by omega) (by omega)).trans hd1)
  have hf2 : f.val.tapes 2 = BitTape.shiftedEnd num origin := by
    exact (hff.2.2.2.2.2.1 2 (by omega) (by omega)).trans
      ((hef.2.2.2.2.2.1 2 (by omega) (by omega)).trans (by
        simpa only [magnitude_eq, d, Store.ofState, num] using hd2))
  have hr := WordTransfer.rewind_shifted 2 origin input tape num f.val f.property hf2
  let r : Store := Store.ofState (Rewind.finishAt 2 origin f.val)
  have her : Executes input tape (.call (Rewind.program 2)) (4 * num.length + 6) f r :=
    Executes.call _ _ _ _ hr.1 (by simp [Rewind.program, Rewind.finishAt])
  have hrf := WordTransfer.frame_rewind 2 2 2 (Or.inl rfl) origin f.val
  have hfb (i : ℕ) (hi : 3 ≤ i) : f.val.tapes i = s.val.tapes i :=
    (hff.2.2.2.2.2.1 i (by omega) (by omega)).trans
      ((hef.2.2.2.2.2.1 i (by omega) (by omega)).trans
        ((hdf.2.2.2.2.2.1 i hi).trans ((hbt i (by omega)).trans (hat i (by omega)))))
  obtain ⟨moved, hem, hemp, hem2, hem34, hemf⟩ := WordTransfer.move_steps 2 34
    (by omega) input tape num origin outOrigin r.val r.property hr.2
    ((hrf.2.2.2.2.2.1 34 (by omega) (by omega)).trans ((hfb 34 (by omega)).trans h34))
  let t : Store := Store.ofState moved
  have het : Executes input tape (.call (WordTransfer.move 2 34)) (12 * num.length + 11) r t :=
    Executes.call _ _ _ _ hem (by
      simp [WordTransfer.move, hemp, TapeOps.copyClear, Rewind.program, BitRAMInstruction.relocate])
  refine ⟨(15 * (v 30).bits.length + 17) + ((15 * (v 31).bits.length + 17) +
      ((diffCost + 1) + ((4 * distance + 6 * ps.length + 11) +
      ((4 * distance + 6 * qs.length + 11) + ((4 * num.length + 6) +
        (12 * num.length + 11)))))), t, ?_,
    hea.seq (heb.seq (hed'.seq (hee.seq (hef'.seq (her.seq het))))), ?_, ?_, ?_, ?_⟩
  · have hpLength := SignedDifference.padded_length (v 30).bits
    have hqLength := SignedDifference.padded_length (v 31).bits
    have hnLength := magnitude_bits_length_le (v 30) (v 31)
    dsimp [distance, ps, qs, num]
    omega
  · intro i hi hi'
    by_cases he : i = 34
    · subst i
      exact ⟨outOrigin, by simpa only [Function.update_self, t, Store.ofState, num] using hem34⟩
    · simp only [Function.update_of_ne he]
      exact word_of_eq ((hemf.2.2.2.2.2.1 i (by omega) he).trans
        ((hrf.2.2.2.2.2.1 i (by omega) (by omega)).trans (hfb i (by omega)))) (hbank i hi hi')
  · refine ⟨blank_of_eq ((hemf.2.2.2.2.2.1 0 (by omega) (by omega)).trans
        ((hrf.2.2.2.2.2.1 0 (by omega) (by omega)).trans
          (hff.2.2.2.2.2.1 0 (by omega) (by omega)))) he0,
      (zero_word_iff_blank _ _).mpr (blank_of_eq
        ((hemf.2.2.2.2.2.1 1 (by omega) (by omega)).trans
          (hrf.2.2.2.2.2.1 1 (by omega) (by omega))) hf1),
      ⟨origin + num.length, hem2⟩, ⟨yo, ?_⟩⟩
    exact (hemf.2.2.2.2.2.1 3 (by omega) (by omega)).trans
      ((hrf.2.2.2.2.2.1 3 (by omega) (by omega)).trans ((hfb 3 (by omega)).trans h3))
  · exact ((((((transfer_frame (Or.inr (by omega)) (Or.inl (by omega)) hcaf).trans
      (transfer_frame (Or.inr (by omega)) (Or.inl (by omega)) hcbf)).trans
      (difference_frame hdf)).trans
      (transfer_frame (Or.inl (by omega)) (Or.inl (by omega)) hef)).trans
      (transfer_frame (Or.inl (by omega)) (Or.inl (by omega)) hff)).trans
      (transfer_frame (Or.inl (by omega)) (Or.inl (by omega)) hrf)).trans
      (transfer_frame (Or.inl (by omega)) (Or.inr (by omega)) hemf)

  · exact (hemf.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)).trans
      ((hrf.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)).trans
        ((hff.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)).trans
          ((hef.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)).trans hdSign)))

/-- Compatibility statement for clients needing only the absolute value. -/
theorem store_magnitude (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) (hzero : v 34 = 0) :
    ∃ cost, ∃ t : Store,
      cost ≤ 300 * ((v 30).bits.length + (v 31).bits.length + 4) ∧
      Executes input tape magnitudeCode cost s t ∧
      Bank t.val (Function.update v 34 (magnitude (v 30) (v 31))) ∧
      Scratch t.val 0 ∧ DyadicSqrt.Frame s.val t.val := by
  obtain ⟨cost, t, hc, he, hb, hs, hf, _⟩ :=
    store_magnitude_signed input tape v s hbank hready hzero
  exact ⟨cost, t, hc, he, hb, hs, hf⟩

end Maxwell.Cost.IntegerNormSquare
