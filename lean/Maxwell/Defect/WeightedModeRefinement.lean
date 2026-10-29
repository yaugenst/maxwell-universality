import Maxwell.Defect.DyadicSqrt
import Maxwell.Defect.ModeCertificate
import Maxwell.Defect.PowerRefinement

/-! Executable rational weighted eigenvector and eigenvalue refinement.
One additional precision bit pays for both the weight and vector errors. -/

namespace Maxwell.Defect.WeightedModeRefinement

open InnerProductSpace Matrix

variable {n : ℕ}

def weightedVector (W : Fin n → ℚ) (q : ℕ → Fin n → ℚ) (b : ℕ) : Fin n → ℚ :=
  fun i => DyadicSqrt.weight (W i) (b + 1) * q (b + 1) i

theorem weightedVector_cast (W : Fin n → ℚ) (q : ℕ → Fin n → ℚ) (b : ℕ) :
    rationalVector (weightedVector W q b) =
      rationalOperator (Matrix.diagonal (fun i => DyadicSqrt.weight (W i) (b + 1)))
        (rationalVector (q (b + 1))) := by
  rw [rationalOperator_diagonal]
  ext i
  simp [weightedVector, rationalVector, weight_diagonal_apply]

/-- The rational source has norm at most one and approximates the actual
square-root-weighted unit eigenvector to the requested dyadic accuracy. -/
theorem weightedVector_spec (W : Fin n → ℚ) (q : ℕ → Fin n → ℚ)
    (u : EuclideanSpace ℝ (Fin n))
    (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) (hu : ‖u‖ = 1)
    (hqnorm : ∀ b, ‖rationalVector (q b)‖ ≤ 1)
    (hqerror : ∀ b, ‖rationalVector (q b) - u‖ ≤ ((2 : ℝ) ^ b)⁻¹) (b : ℕ) :
    ‖rationalVector (weightedVector W q b)‖ ≤ 1 ∧
      ‖rationalVector (weightedVector W q b) - sqrtWeightOperator W u‖ ≤
        ((2 : ℝ) ^ b)⁻¹ := by
  let L := rationalOperator (Matrix.diagonal (fun i => DyadicSqrt.weight (W i) (b + 1)))
  let D := sqrtWeightOperator W
  have hb := rational_weight_operator_bounds W (fun i => DyadicSqrt.weight (W i) (b + 1))
    (((2 : ℚ) ^ (b + 1))⁻¹) hW hW1 (by positivity)
    (fun i => DyadicSqrt.weight_spec (W i) (hW i) (hW1 i) (b + 1))
  have hL : ‖L‖ ≤ 1 := hb.2.1
  have hLD : ‖L - D‖ ≤ ((2 : ℝ) ^ (b + 1))⁻¹ := by
    simpa only [Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat] using hb.2.2
  rw [weightedVector_cast]
  change ‖L (rationalVector (q (b + 1)))‖ ≤ 1 ∧
    ‖L (rationalVector (q (b + 1))) - D u‖ ≤ _
  constructor
  · calc
      _ ≤ ‖L‖ * ‖rationalVector (q (b + 1))‖ := L.le_opNorm _
      _ ≤ 1 * 1 := by gcongr; exact hqnorm _
      _ = 1 := one_mul _
  · have hid : L (rationalVector (q (b + 1))) - D u =
        L (rationalVector (q (b + 1)) - u) + (L - D) u := by
      rw [map_sub, _root_.sub_apply]
      abel
    rw [hid]
    calc
      _ ≤ ‖L (rationalVector (q (b + 1)) - u)‖ + ‖(L - D) u‖ := norm_add_le _ _
      _ ≤ ‖L‖ * ‖rationalVector (q (b + 1)) - u‖ + ‖L - D‖ * ‖u‖ :=
        add_le_add (L.le_opNorm _) ((L - D).le_opNorm _)
      _ ≤ 1 * ((2 : ℝ) ^ (b + 1))⁻¹ + ((2 : ℝ) ^ (b + 1))⁻¹ * 1 := by
        rw [hu]
        gcongr
        exact hqerror _
      _ = _ := by rw [pow_succ]; ring

def eigenvalue (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (q : ℕ → Fin n → ℚ)
    (b : ℕ) : ℚ := rationalOverlap (q b) (T b *ᵥ q b)

theorem eigenvalue_cast (T : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (q : ℕ → Fin n → ℚ) (b : ℕ) :
    (eigenvalue T q b : ℝ) =
      inner ℝ (rationalVector (q b)) (rationalOperator (T b) (rationalVector (q b))) := by
  rw [eigenvalue, rationalOverlap_cast, rationalVector_mulVec]

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem quadratic_eigenvalue_error (S T : E →L[ℝ] E) (q u : E) (μ ε d : ℝ)
    (hu : ‖u‖ = 1) (heig : S u = μ • u) (hq : ‖q‖ ≤ 1)
    (hT : ‖T - S‖ ≤ ε) (hd : ‖q - u‖ ≤ d) :
    |inner ℝ q (T q) - μ| ≤ ε + 2 * ‖S‖ * d := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hT
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  have hcenter : inner ℝ u (S u) = μ := by
    rw [heig, inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
  have hfirst : |inner ℝ q (T q) - inner ℝ q (S q)| ≤ ε := by
    rw [← inner_sub_right, ← _root_.sub_apply]
    calc
      _ ≤ ‖q‖ * ‖(T - S) q‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖q‖ * (‖T - S‖ * ‖q‖) :=
        mul_le_mul_of_nonneg_left ((T - S).le_opNorm _) (norm_nonneg _)
      _ ≤ 1 * (ε * 1) := by gcongr
      _ = ε := by ring
  have hsecond : |inner ℝ q (S q) - inner ℝ u (S u)| ≤ 2 * ‖S‖ * d := by
    have hid : inner ℝ q (S q) - inner ℝ u (S u) =
        inner ℝ (q - u) (S q) + inner ℝ u (S (q - u)) := by
      rw [inner_sub_left, map_sub, inner_sub_right]
      ring
    rw [hid]
    calc
      _ ≤ |inner ℝ (q - u) (S q)| + |inner ℝ u (S (q - u))| := abs_add_le _ _
      _ ≤ ‖q - u‖ * ‖S q‖ + ‖u‖ * ‖S (q - u)‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
      _ ≤ ‖q - u‖ * (‖S‖ * ‖q‖) + ‖u‖ * (‖S‖ * ‖q - u‖) := by
        gcongr
        · exact S.le_opNorm _
        · exact S.le_opNorm _
      _ ≤ d * (‖S‖ * 1) + 1 * (‖S‖ * d) := by rw [hu]; gcongr
      _ = _ := by ring
  rw [← hcenter]
  exact (abs_sub_le _ _ _).trans (add_le_add hfirst hsecond)

end Quadratic

/-- The rational quadratic form approximates the same actual eigenvalue;
the norm-one cap avoids any normalization quotient in the executable code. -/
theorem eigenvalue_spec (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (q : ℕ → Fin n → ℚ)
    (u : EuclideanSpace ℝ (Fin n)) (μ C : ℝ)
    (hu : ‖u‖ = 1) (heig : S u = μ • u)
    (hqnorm : ∀ b, ‖rationalVector (q b)‖ ≤ 1)
    (hqerror : ∀ b, ‖rationalVector (q b) - u‖ ≤ ((2 : ℝ) ^ b)⁻¹)
    (hTerror : ∀ b, ‖rationalOperator (T b) - S‖ ≤ C * ((2 : ℝ) ^ b)⁻¹) (b : ℕ) :
    |(eigenvalue T q b : ℝ) - μ| ≤ (C + 2 * ‖S‖) * ((2 : ℝ) ^ b)⁻¹ := by
  rw [eigenvalue_cast]
  convert quadratic_eigenvalue_error S (rationalOperator (T b)) (rationalVector (q b)) u
    μ (C * ((2 : ℝ) ^ b)⁻¹) (((2 : ℝ) ^ b)⁻¹) hu heig (hqnorm b) (hTerror b) (hqerror b)
    using 1
  ring

end Maxwell.Defect.WeightedModeRefinement
