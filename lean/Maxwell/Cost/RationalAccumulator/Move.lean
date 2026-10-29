import Maxwell.Cost.RationalAccumulator.Bank

namespace Maxwell.Cost.RationalAccumulator

open Structured

theorem move_to_one (source : ℕ) (hs : 30 ≤ source) (hs' : source ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ t : Store, Executes input tape (.call (WordTransfer.move source 1))
      (12 * (v source).bits.length + 11) s t ∧
      Bank t.val (Function.update v source 0) ∧ Scratch t.val (v source) ∧ Frame s.val t.val := by
  obtain ⟨so, hsource⟩ := hbank source hs hs'
  obtain ⟨xo, hone⟩ := (zero_word_iff_blank s.val 1).mp hready.2.1
  obtain ⟨t, ht, hp, hts, htt, hf⟩ := WordTransfer.move_steps source 1 (by omega)
    input tape (v source).bits so xo s.val s.property hsource hone
  refine ⟨Store.ofState t, ?_, ?_, ?_, clone_frame (Or.inr ⟨hs, hs'⟩) (Or.inl (by omega)) hf⟩
  · exact Executes.call _ _ _ _ ht (by
      simp [WordTransfer.move, hp, TapeOps.copyClear, Rewind.program, BitRAMInstruction.relocate])
  · intro i hi hi'
    by_cases he : i = source
    · subst i
      simp only [Function.update_self, zero_word_iff_blank]
      exact ⟨so + (v source).bits.length, hts⟩
    · simp only [Function.update_of_ne he]
      exact word_of_eq (hf.2.2.2.2.2.1 i he (by omega)) (hbank i hi hi')
  · exact ⟨blank_of_eq (hf.2.2.2.2.2.1 0 (by omega) (by omega)) hready.1,
      ⟨xo, htt⟩, blank_of_eq (hf.2.2.2.2.2.1 2 (by omega) (by omega)) hready.2.2.1,
      blank_of_eq (hf.2.2.2.2.2.1 3 (by omega) (by omega)) hready.2.2.2⟩

theorem bits_mul_le (a b : ℕ) : (a * b).bits.length ≤ a.bits.length + b.bits.length := by
  simpa only [Codec.unsignedBitLength_eq_size, Nat.size_eq_bits_len] using Codec.unsignedBitLength_mul_le a b

theorem bits_add_le (a b : ℕ) :
    (a + b).bits.length ≤ max a.bits.length b.bits.length + 1 := by
  simpa only [Codec.unsignedBitLength_eq_size, Nat.size_eq_bits_len] using Codec.unsignedBitLength_add_le a b

end Maxwell.Cost.RationalAccumulator
