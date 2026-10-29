import Maxwell.Codec
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise

namespace Maxwell.Cost.RealNatCode

/-- One descending binary decision, derived from actual subtraction. -/
theorem remainder_step (n k : ℕ) :
    (if 2 ^ k ≤ n % 2 ^ (k + 1) then n % 2 ^ (k + 1) - 2 ^ k
      else n % 2 ^ (k + 1)) = n % 2 ^ k := by
  rw [pow_succ]
  let r := n % (2 ^ k * 2)
  have hr : r < 2 ^ k * 2 := Nat.mod_lt n (Nat.mul_pos (Nat.two_pow_pos k) (by decide))
  have he : r % 2 ^ k = n % 2 ^ k := Nat.mod_mul_right_mod n (2 ^ k) 2
  change (if 2 ^ k ≤ r then r - 2 ^ k else r) = n % 2 ^ k
  rw [← he]
  by_cases h : 2 ^ k ≤ r
  · rw [ite_eq_left h, Nat.mod_eq_sub_mod h]
    exact (Nat.mod_eq_of_lt (by omega : r - 2 ^ k < 2 ^ k)).symm
  · rw [ite_eq_right h]
    exact (Nat.mod_eq_of_lt (by omega : r < 2 ^ k)).symm

theorem bit_decision (n k : ℕ) :
    decide (2 ^ k ≤ n % 2 ^ (k + 1)) = n.testBit k := by
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.mod_mul_right_div_self n (2 ^ k) 2,
    pow_succ]
  have hr := Nat.mod_lt n (Nat.two_pow_pos (k + 1))
  rw [pow_succ] at hr
  by_cases h : 2 ^ k ≤ n % (2 ^ k * 2)
  · have hd : n % (2 ^ k * 2) / 2 ^ k = 1 :=
      Nat.div_eq_of_lt_le (by simpa using h) (by simpa [Nat.mul_comm] using hr)
    simp [h, hd]
  · have hd : n % (2 ^ k * 2) / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, hd]

theorem code_length (n : ℕ) : (Codec.nat n).length = 2 * n.size + 1 := by
  simp [Codec.nat, Nat.size_eq_bits_len]
  omega

/-- Pointwise characterization of the actual self-delimiting codec. -/
theorem code_get (n j : ℕ) (hj : j < (Codec.nat n).length) :
    (Codec.nat n)[j]?.getD false =
      if j < n.size then true else if j = n.size then false else n.testBit (j - n.size - 1) := by
  by_cases hlt : j < n.size
  · simp [Codec.nat, List.getElem?_append, Nat.size_eq_bits_len, hlt]
  · by_cases heq : j = n.size
    · subst j
      simp [Codec.nat, Nat.size_eq_bits_len]
    · have hsub : j - n.size = (j - n.size - 1) + 1 := by omega
      rw [ite_eq_right hlt, ite_eq_right heq]
      have hsize : j - n.size - 1 < n.bits.length := by
        rw [code_length] at hj
        rw [Nat.size_eq_bits_len]
        omega
      simp only [Codec.nat, List.getElem?_append, List.length_replicate,
        Nat.size_eq_bits_len, hlt, ↓reduceIte]
      rw [hsub, List.getElem?_cons_succ, Nat.testBit_eq_inth]
      simp [List.getI, hsize]

end Maxwell.Cost.RealNatCode
