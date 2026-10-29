import Maxwell.Cost.CalibrationMatrix.Accumulate

namespace Maxwell.Cost.CalibrationMatrix

open Structured RationalAccumulator

def signedMacCode : Code := .seq (macCode 32 34 30) (.seq (macCode 33 35 30)
  (.seq (macCode 32 35 31) (macCode 33 34 31)))

def signedAccumulated (v : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update v 30 (v 30+v 32*v 34+v 33*v 35))
    31 (v 31+v 32*v 35+v 33*v 34)

theorem signed_mac (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (B : ℕ)
    (hbits : ∀ i, 30 ≤ i → i ≤ 35 → (v i).bits.length ≤ B)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0) (hz : v 36 = 0) :
    ∃ cost, ∃ t : Store, cost ≤ 400000*(B+2)^2 ∧
      Executes input tape signedMacCode cost s t ∧
      Bank t.val (signedAccumulated v) ∧ Scratch t.val 0 ∧ RationalAccumulator.Frame s.val t.val := by
  let v1 := accumulated v 32 34 30
  let v2 := accumulated v1 33 35 30
  let v3 := accumulated v2 32 35 31
  obtain ⟨c1, a, hc1, ha, hab, har, haf⟩ := mac 32 34 30 (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) input tape v s hbank hready hz
  obtain ⟨c2, b, hc2, hb, hbb, hbr, hbf⟩ := mac 33 35 30 (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) input tape v1 a hab har (by simp [v1, accumulated, hz])
  obtain ⟨c3, c, hc3, hc, hcb, hcr, hcf⟩ := mac 32 35 31 (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) input tape v2 b hbb hbr (by simp [v2, v1, accumulated, hz])
  obtain ⟨c4, t, hc4, ht, htb, htr, htf⟩ := mac 33 34 31 (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) input tape v3 c hcb hcr
    (by simp [v3, v2, v1, accumulated, hz])
  have hvalues : accumulated v3 33 34 31 = signedAccumulated v := by
    funext i
    by_cases h30 : i = 30
    · subst i; simp [v3, v2, v1, accumulated, signedAccumulated]; ring
    · by_cases h31 : i = 31
      · subst i; simp [v3, v2, v1, accumulated, signedAccumulated]; ring
      · simp [v3, v2, v1, accumulated, signedAccumulated, h30, h31]
  refine ⟨c1+(c2+(c3+c4)), t, ?_, ha.seq (hb.seq (hc.seq ht)), hvalues ▸ htb, htr,
    ((haf.trans hbf).trans hcf).trans htf⟩
  have h30 := hbits 30 (by omega) (by omega)
  have h31 := hbits 31 (by omega) (by omega)
  have h32 := hbits 32 (by omega) (by omega)
  have h33 := hbits 33 (by omega) (by omega)
  have h34 := hbits 34 (by omega) (by omega)
  have h35 := hbits 35 (by omega) (by omega)
  have hp30 := bits_mul_le (v 34) (v 32)
  have hp31 := bits_mul_le (v 35) (v 32)
  have hs30 := bits_add_le (v 34*v 32) (v 30)
  have hs31 := bits_add_le (v 35*v 32) (v 31)
  have hm30 : max (v 34*v 32).bits.length (v 30).bits.length ≤ 2*B := max_le (by omega) (by omega)
  have hm31 : max (v 35*v 32).bits.length (v 31).bits.length ≤ 2*B := max_le (by omega) (by omega)
  simp only [v3, v2, v1, accumulated, Function.update_apply] at hc2 hc3 hc4
  norm_num at hc2 hc3 hc4
  have hb1 : c1 ≤ 5000*(4*B+5)^2 := hc1.trans
    (Nat.mul_le_mul_left 5000 (Nat.pow_le_pow_left (by omega) 2))
  have hb2 : c2 ≤ 5000*(4*B+5)^2 := hc2.trans
    (Nat.mul_le_mul_left 5000 (Nat.pow_le_pow_left (by omega) 2))
  have hb3 : c3 ≤ 5000*(4*B+5)^2 := hc3.trans
    (Nat.mul_le_mul_left 5000 (Nat.pow_le_pow_left (by omega) 2))
  have hb4 : c4 ≤ 5000*(4*B+5)^2 := hc4.trans
    (Nat.mul_le_mul_left 5000 (Nat.pow_le_pow_left (by omega) 2))
  nlinarith

end Maxwell.Cost.CalibrationMatrix
