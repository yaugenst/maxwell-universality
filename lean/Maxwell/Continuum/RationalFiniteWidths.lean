import Maxwell.Continuum.RationalArithmeticWidths

/-! Operand widths for finite rational products, powers, and sums. -/

namespace Maxwell.Continuum.RationalWords

theorem width_zero' : Width 0 1 := by constructor <;> decide

theorem Width.pow {q : ℚ} {B : ℕ} (hq : Width q B) (n : ℕ) :
    Width (q^n) (n*B+1) := by
  induction n with
  | zero => simpa using width_one
  | succ n ih =>
    rw [pow_succ]
    convert ih.mul hq using 1
    ring

theorem width_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (B : ℕ)
    (hf : ∀ i∈s, Width (f i) B) : Width (∑ i∈s, f i) (s.card*(B+1)+1) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simpa using width_zero'
  | @insert a s ha ih =>
    intro hf
    rw [Finset.sum_insert ha,Finset.card_insert_of_notMem ha]
    have hs := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    convert (hf a (Finset.mem_insert_self a s)).add hs using 1
    ring

theorem width_int (z : ℤ) : Width (z : ℚ) (z.natAbs.bits.length+1) := by
  constructor
  · simp
  · simp

theorem width_nat (n : ℕ) : Width (n : ℚ) (n+1) := by
  have h := width_int (n : ℤ)
  have hs : n.bits.length≤n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
  have hn : Width (n : ℚ) (n.bits.length+1) := by
    simpa only [Int.natAbs_natCast,Int.cast_natCast] using h
  exact hn.mono (by omega)

theorem width_fraction {z : ℤ} {d B : ℕ} (hd : 0<d)
    (hz : z.natAbs.bits.length≤B) (hden : d.bits.length≤B) : Width ((z : ℚ)/d) B :=
  ⟨(bits_mono (reduced_numerator z d hd)).trans hz,
    (bits_mono (reduced_denominator z d hd)).trans hden⟩

#print axioms width_sum

end Maxwell.Continuum.RationalWords
