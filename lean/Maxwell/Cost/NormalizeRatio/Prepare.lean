import Maxwell.Cost.RationalAccumulator.Move

/-! Actual integer cross products for a normalized dyadic coefficient. The
input coefficient and selected scale retain their original rational pairs. -/
namespace Maxwell.Cost.NormalizeRatio
open Structured RationalAccumulator

/-- Tapes 30/31 hold the unsigned coefficient, 32/33 the positive scale,
and 34 the dyadic denominator. Tapes 35/36 receive the scaled quotient's
numerator and denominator. -/
def prepareCode : Code :=
  Code.seq (.call (WordTransfer.clone 30 35)) <|
  Code.seq (.call (WordTransfer.clone 31 36)) <|
  Code.seq (.call (WordTransfer.clone 33 1)) <|
  Code.seq (.call (StoredProduct.program 35)) <|
  Code.seq (.call (TapeOps.clear 1)) <|
  Code.seq (.call (WordTransfer.clone 34 1)) <|
  Code.seq (.call (StoredProduct.program 35)) <|
  Code.seq (.call (TapeOps.clear 1)) <|
  Code.seq (.call (WordTransfer.clone 32 1)) <|
  Code.seq (.call (StoredProduct.program 36)) <|
  .call (TapeOps.clear 1)

def prepared (v : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update v 35 (v 34 * (v 33 * v 30))) 36 (v 32 * v 31)

theorem prepare (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (B : ℕ)
    (hbits : ∀ i, 30 ≤ i → i ≤ 34 → (v i).bits.length ≤ B)
    (hscaleNum : 0 < v 32) (hscaleDen : 0 < v 33) (hpower : 0 < v 34)
    (hz35 : v 35 = 0) (hz36 : v 36 = 0)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store, cost ≤ 20000*(B+2)^2 ∧
      Executes input tape prepareCode cost s t ∧
      Bank t.val (prepared v) ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨s1, h1, hb1, hr1, hf1⟩ := clone_bank 30 35 (by decide) (by decide)
    (by decide) (by decide) (by decide) input tape v 0 s hbank hz35 hready
  let v1 := Function.update v 35 (v 30)
  obtain ⟨s2, h2, hb2, hr2, hf2⟩ := clone_bank 31 36 (by decide) (by decide)
    (by decide) (by decide) (by decide) input tape v1 0 s1 hb1
    (by simpa [v1] using hz36) hr1
  let v2 := Function.update v1 36 (v1 31)
  have hv233 : v2 33 = v 33 := by simp [v2, v1]
  obtain ⟨s3, h3, hb3, hr3, hf3⟩ := clone_to_one 33 (by decide) (by decide)
    input tape v2 s2 hb2 hr2
  rw [hv233] at hr3
  obtain ⟨c4, s4, hc4, h4, hb4, hr4, hf4⟩ := multiply_bank 35 (by decide) (by decide)
    input tape v2 (v 33) hscaleDen s3 hb3 hr3
  let v3 := Function.update v2 35 (v 33 * v2 35)
  obtain ⟨s5, h5, hb5, hr5, hf5⟩ := clear_one input tape v3 (v 33) s4 hb4 hr4
  have hv334 : v3 34 = v 34 := by simp [v3, v2, v1]
  obtain ⟨s6, h6, hb6, hr6, hf6⟩ := clone_to_one 34 (by decide) (by decide)
    input tape v3 s5 hb5 hr5
  rw [hv334] at hr6
  obtain ⟨c7, s7, hc7, h7, hb7, hr7, hf7⟩ := multiply_bank 35 (by decide) (by decide)
    input tape v3 (v 34) hpower s6 hb6 hr6
  let v4 := Function.update v3 35 (v 34 * v3 35)
  obtain ⟨s8, h8, hb8, hr8, hf8⟩ := clear_one input tape v4 (v 34) s7 hb7 hr7
  have hv432 : v4 32 = v 32 := by simp [v4, v3, v2, v1]
  obtain ⟨s9, h9, hb9, hr9, hf9⟩ := clone_to_one 32 (by decide) (by decide)
    input tape v4 s8 hb8 hr8
  rw [hv432] at hr9
  obtain ⟨c10, s10, hc10, h10, hb10, hr10, hf10⟩ := multiply_bank 36 (by decide) (by decide)
    input tape v4 (v 32) hscaleNum s9 hb9 hr9
  let v5 := Function.update v4 36 (v 32 * v4 36)
  obtain ⟨s11, h11, hb11, hr11, hf11⟩ := clear_one input tape v5 (v 32) s10 hb10 hr10
  have hv5 : v5 = prepared v := by
    ext i
    by_cases h35 : i = 35 <;> by_cases h36 : i = 36 <;>
      simp_all [v5, v4, v3, v2, v1, prepared]
  refine ⟨(15*(v 30).bits.length+17) + ((15*(v1 31).bits.length+17) +
      ((15*(v2 33).bits.length+17) + (c4 + ((6*(v 33).bits.length+4) +
      ((15*(v3 34).bits.length+17) + (c7 + ((6*(v 34).bits.length+4) +
      ((15*(v4 32).bits.length+17) + (c10 + (6*(v 32).bits.length+4)))))))))),
    s11, ?_, h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq
      (h9.seq (h10.seq h11))))))))), hv5 ▸ hb11, hr11,
    hf1.trans (hf2.trans (hf3.trans (hf4.trans (hf5.trans (hf6.trans (hf7.trans
      (hf8.trans (hf9.trans (hf10.trans hf11)))))))))⟩
  have h30 := hbits 30 (by decide) (by decide)
  have h31 := hbits 31 (by decide) (by decide)
  have h32 := hbits 32 (by decide) (by decide)
  have h33 := hbits 33 (by decide) (by decide)
  have h34 := hbits 34 (by decide) (by decide)
  have hm : (v 33 * v 30).bits.length ≤ 2*B :=
    (bits_mul_le _ _).trans (by omega)
  simp [v4, v3, v2, v1] at hc4 hc7 hc10 ⊢
  have h4bound : c4 ≤ 500*(2*B+2)^2+1 := hc4.trans (by gcongr; omega)
  have h7bound : c7 ≤ 500*(3*B+2)^2+1 := hc7.trans (by gcongr; omega)
  have h10bound : c10 ≤ 500*(2*B+2)^2+1 := hc10.trans (by gcongr; omega)
  nlinarith

theorem prepared_denominator_pos (v : ℕ → ℕ) (hq : 0 < v 31) (hs : 0 < v 32) :
    0 < prepared v 36 := by simpa [prepared] using Nat.mul_pos hs hq

theorem prepared_value (v : ℕ → ℕ) (negative : Bool) :
    (if negative then -(prepared v 35 : ℚ) else prepared v 35) / prepared v 36 =
      ((if negative then -(v 30:ℚ) else v 30) / v 31) /
        ((v 32:ℚ)/v 33) * v 34 := by
  cases negative <;> simp [prepared, div_eq_mul_inv, mul_inv_rev, inv_inv] <;> ring

theorem prepared_bits (v : ℕ → ℕ) (B : ℕ)
    (hbits : ∀ i, 30 ≤ i → i ≤ 34 → (v i).bits.length ≤ B) :
    (prepared v 35).bits.length ≤ 3*B ∧ (prepared v 36).bits.length ≤ 2*B := by
  have h30 := hbits 30 (by decide) (by decide)
  have h31 := hbits 31 (by decide) (by decide)
  have h32 := hbits 32 (by decide) (by decide)
  have h33 := hbits 33 (by decide) (by decide)
  have h34 := hbits 34 (by decide) (by decide)
  simp only [prepared, Function.update_self, Function.update_of_ne (show 35 ≠ 36 by decide)]
  constructor
  · exact (bits_mul_le _ _).trans (by have h := bits_mul_le (v 33) (v 30); omega)
  · exact (bits_mul_le _ _).trans (by omega)

end Maxwell.Cost.NormalizeRatio
