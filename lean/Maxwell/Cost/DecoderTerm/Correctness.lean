import Maxwell.Cost.DecoderTerm
import Maxwell.Cost.RationalAccumulator.Push

namespace Maxwell.Cost.DecoderTerm
open Structured
open RationalAccumulator (Word Blank Bank Scratch)

def termBank (v : ℕ → ℕ) (mag den : ℕ) : ℕ → ℕ :=
  Function.update (Function.update v 33 mag) 34 den

theorem bank_after {s t : BitRAMState} {v : ℕ → ℕ} {mag den : ℕ}
    (hf : Frame s t) (hb : Bank s v) (h33 : Word t 33 mag) (h34 : Word t 34 den) :
    Bank t (termBank v mag den) := by
  intro i hi hi'
  by_cases h34' : i = 34
  · subst i; simpa [termBank] using h34
  by_cases h33' : i = 33
  · subst i; simpa [termBank] using h33
  simp only [termBank,Function.update_of_ne h34',Function.update_of_ne h33']
  exact RationalAccumulator.word_of_eq
    (hf.2.2.2.2.2.1 i (by omega) (by omega) (by omega) (by omega) h33' h34' (by omega)) (hb i hi hi')

theorem scratch_after {s : BitRAMState} (h : ∀ i, i < 4 → Blank s i) : Scratch s 0 :=
  ⟨h 0 (by omega),(RationalAccumulator.zero_word_iff_blank s 1).mpr (h 1 (by omega)),
    h 2 (by omega),h 3 (by omega)⟩

/-- The machine-computed term is exactly the public offset-binary access
value multiplied by the parsed rational weight. No accuracy hypothesis or
arithmetic oracle is needed for this equality. -/
theorem fixedPoint_executes (input : List Bool) (randomTape : ℕ → Bool)
    (F : Target.FixedPointFormat) (w : F.Word) (q : ℚ) (sample : List Bool)
    (hsample : addressValue sample = w.val) (sampleOrigin : ℤ) (v : ℕ → ℕ) (s : Store)
    (h7 : s.val.tapes 7 = BitTape.shiftedEnd sample sampleOrigin)
    (h12 : s.val.tapes 12 = BitTape.atEnd q.num.natAbs.bits)
    (h13 : s.val.tapes 13 = BitTape.atEnd q.den.bits)
    (hsign : s.val.registers 23 = decide (q.num < 0))
    (h66 : Word s.val 66 (2^(F.integerBits+F.fractionalBits)))
    (h67 : Word s.val 67 (2^F.fractionalBits))
    (hbank : Bank s.val v) (h33 : v 33 = 0) (h34 : v 34 = 0)
    (hscratch : Scratch s.val 0) (h65 : Blank s.val 65) :
    ∃ cost, ∃ t : Store,
      cost ≤ costBound sample (2^(F.integerBits+F.fractionalBits)) (2^F.fractionalBits) q.num.natAbs q.den ∧
      Executes input randomTape code cost s t ∧
      Bank t.val (termBank v (magnitude sample (2^(F.integerBits+F.fractionalBits))*q.num.natAbs)
        ((2^F.fractionalBits)*q.den)) ∧ Scratch t.val 0 ∧
      RationalAccumulator.termValue
        (termBank v (magnitude sample (2^(F.integerBits+F.fractionalBits))*q.num.natAbs)
          ((2^F.fractionalBits)*q.den)) (t.val.registers 35) = q*F.value w ∧
      0 < (termBank v (magnitude sample (2^(F.integerBits+F.fractionalBits))*q.num.natAbs)
        ((2^F.fractionalBits)*q.den)) 34 ∧
      Blank t.val 7 ∧ Blank t.val 65 ∧
      t.val.tapes 12 = BitTape.blank ∧ t.val.tapes 13 = BitTape.blank ∧ Frame s.val t.val := by
  have hb33 : Blank s.val 33 := by
    have h := hbank 33 (by omega) (by omega)
    rw [h33,RationalAccumulator.zero_word_iff_blank] at h
    exact h
  have hb34 : Blank s.val 34 := by
    have h := hbank 34 (by omega) (by omega)
    rw [h34,RationalAccumulator.zero_word_iff_blank] at h
    exact h
  have hblank (i : ℕ) (hi : i < 4) : Blank s.val i := by
    interval_cases i
    · exact hscratch.1
    · exact (RationalAccumulator.zero_word_iff_blank s.val 1).mp hscratch.2.1
    · exact hscratch.2.2.1
    · exact hscratch.2.2.2
  obtain ⟨cost,t,hcost,he,ht33,ht34,htblank,ht7,ht65,ht12,ht13,htsign,hf⟩ :=
    executes input randomTape sample sampleOrigin (2^(F.integerBits+F.fractionalBits))
      (2^F.fractionalBits) q.num.natAbs q.den s h7 h12 h13 h66 h67 hblank hb33 hb34 h65
  refine ⟨cost,t,hcost,he,bank_after hf hbank ht33 ht34,scratch_after htblank,?_,?_,ht7,ht65,ht12,ht13,hf⟩
  · rw [htsign,hsign]
    simpa only [RationalAccumulator.termValue,termBank,Function.update_self,
      Function.update_of_ne (by decide : (33 : ℕ) ≠ 34),signed] using fixedPoint_value F w q sample hsample
  · simp only [termBank,Function.update_self]
    exact Nat.mul_pos (by positivity) q.pos

end Maxwell.Cost.DecoderTerm
