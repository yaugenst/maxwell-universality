import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size

/-! Binary word length and the ceiling logarithm used by finite encoders. -/
namespace Maxwell.Codec

theorem clog_two_succ (n : ℕ) : Nat.clog 2 (n+1)=n.bits.length := by
  rw [Nat.size_eq_bits_len]
  apply Nat.le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by decide)]
    exact Nat.succ_le_of_lt (Nat.lt_size_self n)
  · rw [Nat.size_le]
    have h := Nat.le_pow_clog (by decide : 1<(2:ℕ)) (n+1)
    omega

theorem power_bits_le (a n : ℕ) : (a^n).bits.length≤n*a.bits.length+1 := by
  have hp := Nat.pow_le_pow_left (Nat.lt_size_self a).le n
  rw [← Nat.pow_mul] at hp
  have hs := Nat.size_le_size hp
  rw [Nat.size_pow] at hs
  simpa only [← Nat.size_eq_bits_len,Nat.mul_comm] using hs

end Maxwell.Codec
