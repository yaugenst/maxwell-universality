import Maxwell.Continuum.ParameterBudgetBounds

/-! Explicit binary bounds for the actual three-dimensional box counts and
scaled integer center spans. -/

namespace Maxwell.Continuum.Parameters
open scoped BigOperators

 theorem boxCount_binary {s : Fin 3 → ℕ} {L t a b c : ℕ}
    (hs : ∀ j, (s j : ℚ) ≤ (2 : ℚ)^a) (hL : (L : ℚ) ≤ (2 : ℚ)^b)
    (ht : (t : ℚ) ≤ (2 : ℚ)^c) :
    (boxCount s L t : ℚ) ≤ (2 : ℚ)^(1+3*(a+2*b+c+8)) := by
  have hf (j : Fin 3) : (1+2*boxSide s L t j : ℚ) ≤ (2 : ℚ)^(a+2*b+c+8) := by
    have hLt := binary_mul hL ht (Nat.cast_nonneg t)
    have hsum := binary_add (binary_add (hs j) hL) hLt
    have hhalf := binary_add hsum (show (4 : ℚ) ≤ (2 : ℚ)^2 by norm_num)
    have hfour := binary_mul (show (4 : ℚ) ≤ (2 : ℚ)^2 by norm_num) hhalf
      (by positivity : (0 : ℚ) ≤ (s j : ℚ)+L+(L : ℚ)*t+4)
    have hone := binary_one_add hfour
    convert hone using 1
    · simp only [boxSide, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      ring
    · congr 1
      omega
  have hp := Finset.prod_le_prod₀ (fun j _ => by positivity : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      (0 : ℚ) ≤ 1+2*boxSide s L t j) (fun j _ => hf j)
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℚ) ≤ 2)
  convert hm using 1
  · simp only [boxCount, Nat.cast_mul, Nat.cast_prod, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  · simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [pow_add, pow_one, ← pow_mul]
    congr 2
    omega

/-- The physical centers are integral dilates of fixed logical coordinates;
this is their half-span after the common even translation is removed. -/
def scaledSpan (v : Fin 3 → ℕ) (L d : ℕ) (j : Fin 3) : ℕ := 2*L*d*v j

 theorem scaledSpan_binary {v : Fin 3 → ℕ} {L d a b c : ℕ}
    (hv : ∀ j, (v j : ℚ) ≤ (2 : ℚ)^a) (hL : (L : ℚ) ≤ (2 : ℚ)^b)
    (hd : (d : ℚ) ≤ (2 : ℚ)^c) (j : Fin 3) :
    (scaledSpan v L d j : ℚ) ≤ (2 : ℚ)^(1+b+c+a) := by
  have hp := binary_mul (binary_mul (binary_mul (show (2 : ℚ) ≤ (2 : ℚ)^1 by norm_num)
    hL (Nat.cast_nonneg L)) hd (Nat.cast_nonneg d)) (hv j) (Nat.cast_nonneg _)
  simpa only [scaledSpan, Nat.cast_mul, Nat.cast_ofNat] using hp

 theorem nat_binary_self (n : ℕ) : (n : ℚ) ≤ (2 : ℚ)^n := by
  exact_mod_cast (Nat.lt_two_pow_self (n := n)).le

#print axioms boxCount_binary

end Maxwell.Continuum.Parameters
