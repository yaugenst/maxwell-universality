import Maxwell.Cost.Execution
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.GCD.Basic

/-! The arithmetic invariant and logarithmic iteration bound for the finite
rational-normalization program. These are semantic lemmas, not a runtime
instruction for gcd. -/
namespace Maxwell.Cost.RationalCanonical

def euclid : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, a, b => (a,b)
  | k+1, a, b => if b=0 then (a,0) else euclid k b (a%b)

@[simp] theorem euclid_zero_right (k a : ℕ) : euclid k a 0 = (a,0) := by
  cases k <;> simp [euclid]

theorem euclid_gcd (k a b : ℕ) :
    Nat.gcd (euclid k a b).1 (euclid k a b).2 = Nat.gcd a b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    by_cases hb : b=0
    · simp [euclid,hb]
    · rw [euclid, ite_eq_right hb, ih]
      exact (Nat.gcd_comm b (a%b)).trans
        ((Nat.gcd_rec b a).symm.trans (Nat.gcd_comm b a))

theorem euclid_le (k a b M : ℕ) (ha : a ≤ M) (hb : b ≤ M) :
    (euclid k a b).1 ≤ M ∧ (euclid k a b).2 ≤ M := by
  induction k generalizing a b with
  | zero => exact ⟨ha,hb⟩
  | succ k ih =>
    by_cases hz : b=0
    · simp [euclid,hz,ha]
    · rw [euclid, ite_eq_right hz]
      exact ih b (a%b) hb ((Nat.mod_lt a (Nat.pos_of_ne_zero hz)).le.trans hb)

theorem twice_remainder_lt (b r : ℕ) (hr : 0 < r) (hrb : r < b) : 2*(b%r) < b := by
  by_cases h : 2*r ≤ b
  · have hm := Nat.mod_lt b hr
    omega
  · have hm : b-r < r := by omega
    rw [Nat.mod_eq_sub_mod hrb.le, Nat.mod_eq_of_lt hm]
    omega

/-- Two Euclidean divisions remove at least one bit from the second
operand, so twice its bit length suffices, including zero and unit inputs. -/
theorem euclid_terminal (B a b : ℕ) (hb : b < 2^B) : (euclid (2*B) a b).2 = 0 := by
  induction B generalizing a b with
  | zero =>
    have : b=0 := by simpa using hb
    simp [this]
  | succ B ih =>
    by_cases hb0 : b=0
    · simp [hb0]
    · have hbpos := Nat.pos_of_ne_zero hb0
      have hf : 2*(B+1)=2*B+1+1 := by omega
      rw [hf, euclid, ite_eq_right hb0]
      by_cases hr0 : a%b=0
      · simp [hr0]
      · rw [euclid, ite_eq_right hr0]
        apply ih
        have hh := twice_remainder_lt b (a%b) (Nat.pos_of_ne_zero hr0) (Nat.mod_lt a hbpos)
        rw [pow_succ] at hb
        omega

theorem euclid_size (a b : ℕ) : euclid (2*b.size) a b = (Nat.gcd a b,0) := by
  have hzero := euclid_terminal b.size a b (Nat.lt_size_self b)
  have hg := euclid_gcd (2*b.size) a b
  rw [hzero, Nat.gcd_zero_right] at hg
  exact Prod.ext hg hzero

end Maxwell.Cost.RationalCanonical
