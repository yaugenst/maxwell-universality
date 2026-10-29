import Maxwell.Cost.RationalNormalize.Bank
import Mathlib.Tactic.ClearExcept

namespace Maxwell.Cost.RationalNormalize

open Structured RationalAccumulator

set_option maxHeartbeats 600000

def factorsCode : Code :=
  .seq (loadCode 150 35)
    (.seq (DyadicSqrt.multiplyCode 35 32)
      (.seq (loadCode 151 36) (DyadicSqrt.multiplyCode 36 33)))

def factorsBank (A B m p C D : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (DyadicSqrt.bank A B (C*m) (D*2^p)) 35 C) 36 D

/-- The scalar factors for rational normalization are computed by the
actual stored multiplication routines. The persistent inputs are preserved. -/
theorem factors (input : List Bool) (tape : ℕ → Bool) (A B m p C D W : ℕ)
    (hC : C.bits.length ≤ W) (hD : D.bits.length ≤ W) (hm : m.bits.length ≤ p+1)
    (s : Store) (hbank : Bank s.val (DyadicSqrt.bank A B m (2^p)))
    (hready : Scratch s.val 0) (hCword : Word s.val 150 C) (hDword : Word s.val 151 D) :
    ∃ cost, ∃ t : Store, cost ≤ 3000 * (W+p+4)^2 ∧
      Executes input tape factorsCode cost s t ∧
      Bank t.val (factorsBank A B m p C D) ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨a, e1, b1, r1, f1⟩ := load 150 35 (by omega) (by omega) (by omega)
    input tape (DyadicSqrt.bank A B m (2^p)) C s hbank hready hCword
  let v1 := Function.update (DyadicSqrt.bank A B m (2^p)) 35 C
  obtain ⟨c2, b, hc2, e2, b2, r2, f2⟩ := DyadicSqrt.multiply 35 32
    (by omega) (by omega) (by omega) (by omega) input tape v1 a b1 r1
  let v2 := Function.update v1 32 (C*m)
  change Bank b.val v2 at b2
  have fstart : Frame s.val b.val := f1.trans (frame_of_bank f2)
  have hbD : Word b.val 151 D := word_of_eq
    (fstart.2.2.2.2.2.1 151 (by omega)) hDword
  obtain ⟨c, e3, b3, r3, f3⟩ := load 151 36 (by omega) (by omega) (by omega)
    input tape v2 D b b2 r2 hbD
  let v3 := Function.update v2 36 D
  obtain ⟨c4, t, hc4, e4, b4, r4, f4⟩ := DyadicSqrt.multiply 36 33
    (by omega) (by omega) (by omega) (by omega) input tape v3 c b3 r3
  let v4 := Function.update v3 33 (D*2^p)
  change Bank t.val v4 at b4
  have hvalues : v4 = factorsBank A B m p C D := by
    funext i
    by_cases h30 : i = 30
    · subst i; simp [v4, v3, v2, v1, factorsBank, DyadicSqrt.bank]
    by_cases h31 : i = 31
    · subst i; simp [v4, v3, v2, v1, factorsBank, DyadicSqrt.bank]
    by_cases h32 : i = 32
    · subst i; simp [v4, v3, v2, v1, factorsBank, DyadicSqrt.bank]
    by_cases h33 : i = 33
    · subst i; simp [v4, v3, v2, v1, factorsBank, DyadicSqrt.bank]
    by_cases h35 : i = 35
    · subst i; simp [v4, v3, v2, v1, factorsBank]
    by_cases h36 : i = 36
    · subst i; simp [v4, v3, v2, v1, factorsBank]
    simp [v4, v3, v2, v1, factorsBank, DyadicSqrt.bank, h30, h31, h32, h33, h35, h36]
  refine ⟨(6*(DyadicSqrt.bank A B m (2^p) 35).bits.length+15*C.bits.length+21)+
      (c2+((6*(v2 36).bits.length+15*D.bits.length+21)+c4)), t, ?_,
    e1.seq (e2.seq (e3.seq e4)), hvalues ▸ b4, r4,
    (fstart.trans f3).trans (frame_of_bank f4)⟩
  change c2 ≤ 1200 * (C.bits.length + m.bits.length + 3)^2 at hc2
  change c4 ≤ 1200 * (D.bits.length + (2^p).bits.length + 3)^2 at hc4
  have hpow : (2^p).bits.length = p+1 := by rw [Nat.size_eq_bits_len, Nat.size_pow]
  have hbase2 : C.bits.length+m.bits.length+3 ≤ W+p+4 := by
    clear * - hC hm
    omega
  have hbase4 : D.bits.length+(2^p).bits.length+3 ≤ W+p+4 := by
    rw [hpow]
    clear * - hD
    omega
  have h2 := hc2.trans (Nat.mul_le_mul_left 1200
    (Nat.pow_le_pow_left hbase2 2))
  have h4 := hc4.trans (Nat.mul_le_mul_left 1200
    (Nat.pow_le_pow_left hbase4 2))
  change (6*(0:ℕ).bits.length+15*C.bits.length+21)+
    (c2+((6*(0:ℕ).bits.length+15*D.bits.length+21)+c4)) ≤ _
  rw [show (0:ℕ).bits.length = 0 from rfl]
  have hsq : W+p+4 ≤ (W+p+4)^2 := Nat.le_self_pow (by decide) _
  clear * - hC hD h2 h4 hsq
  omega

end Maxwell.Cost.RationalNormalize
