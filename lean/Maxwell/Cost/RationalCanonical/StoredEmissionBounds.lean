import Maxwell.Cost.RationalCanonical.StoredEmission

/-! Uniform cubic cost for canonical emission from stored signed parts.
Both the input width and the measured old workspace are charged. -/
namespace Maxwell.Cost.RationalCanonical.StoredEmission

theorem costBound_cubic (B H : ℕ) : costBound B H ≤ 1000000*(B+H+4)^3 := by
  have prepare : prepareCost B H ≤ 1000*(B+H+4) := by
    unfold prepareCost
    omega
  have linear : B+H+4 ≤ (B+H+4)^3 := le_self_pow₀ (by omega) (by decide)
  have quadratic : (2*B+3)^3 ≤ (2*(B+H+4))^3 :=
    Nat.pow_le_pow_left (by omega) 3
  unfold costBound
  calc
    _ ≤ 1000*(B+H+4)^3+100000*(2*(B+H+4))^3 :=
      Nat.add_le_add (prepare.trans (Nat.mul_le_mul_left _ linear))
        (Nat.mul_le_mul_left _ quadratic)
    _ ≤ _ := by ring_nf;omega

#print axioms costBound_cubic
end Maxwell.Cost.RationalCanonical.StoredEmission
