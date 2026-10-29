import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-! Exact inverses of every even unweighted path, with odd and even
vertices grouped into two blocks.  This is a closed formula verified by
matrix multiplication, rather than an inverse supplied as a hypothesis. -/

namespace Maxwell.Logical.Path

open Matrix
open scoped Matrix

/-- The subdiagonal shift. -/
def shift (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if j.val + 1 = i.val then 1 else 0

/-- Odd-to-even incidence block of the ordinary unweighted path. -/
def bidiagonal (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := 1 + shift n

/-- Alternating prefix sums give the exact inverse of the incidence block. -/
def prefixInverse (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if j.val ≤ i.val then (-1) ^ (i.val - j.val) else 0

lemma shift_mul_first (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (j : Fin (n + 1)) : (shift (n + 1) * A) 0 j = 0 := by
  simp [Matrix.mul_apply, shift]

lemma shift_mul_succ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (i : Fin n) (j : Fin (n + 1)) :
    (shift (n + 1) * A) i.succ j = A i.castSucc j := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i.castSucc]
  · simp [shift]
  · intro b hb hbi
    have h : b.val ≠ i.val := by
      intro h
      apply hbi
      apply Fin.ext
      simpa using h
    simp [shift, h]
  · simp

lemma prefix_recurrence (n : ℕ) (i : Fin n) (j : Fin (n + 1)) :
    prefixInverse (n + 1) i.succ j + prefixInverse (n + 1) i.castSucc j =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) i.succ j := by
  by_cases h : j.val ≤ i.val
  · have h' : j.val ≤ i.val + 1 := by omega
    have hp : i.val + 1 - j.val = (i.val - j.val) + 1 := by omega
    have hne : i.succ ≠ j := by intro he; have := congrArg Fin.val he; simp at this; omega
    simp [prefixInverse, h, h', hp, pow_succ, hne]
  · by_cases h' : j.val = i.val + 1
    · have he : i.succ = j := by apply Fin.ext; simpa using h'.symm
      subst j
      simp [prefixInverse]
    · have hn : ¬ j.val ≤ i.val + 1 := by omega
      have hne : i.succ ≠ j := by intro he; apply h'; simpa using (congrArg Fin.val he).symm
      simp [prefixInverse, h, hn, hne]

/-- Universally verified left-to-right recurrence, including both path ends. -/
theorem bidiagonal_mul_prefixInverse (n : ℕ) :
    bidiagonal n * prefixInverse n = 1 := by
  cases n with
  | zero => ext i; exact Fin.elim0 i
  | succ n =>
    rw [bidiagonal, Matrix.add_mul, Matrix.one_mul]
    ext i j
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [Matrix.add_apply, shift_mul_first]
      by_cases h : j = 0
      · subst j; simp [prefixInverse]
      · have hj : ¬ j.val ≤ 0 := by
          intro hj
          apply h
          apply Fin.ext
          simpa using (Nat.eq_zero_of_le_zero hj)
        simp [prefixInverse, hj, Ne.symm h]
    · rw [Matrix.add_apply, shift_mul_succ]
      exact prefix_recurrence n k j

/-- The reverse inverse identity follows for finite square matrices. -/
theorem prefixInverse_mul_bidiagonal (n : ℕ) :
    prefixInverse n * bidiagonal n = 1 := by
  exact mul_eq_one_comm.mpr (bidiagonal_mul_prefixInverse n)

/-- The adjacency matrix of the path 0--1--...--(2n-1), with odd/even
vertices grouped.  `inl i` is vertex `2*i`, `inr i` is vertex `2*i+1`. -/
def adjacency (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ :=
  Matrix.fromBlocks 0 (bidiagonal n) (bidiagonal n).transpose 0

/-- Explicit inverse of the even path adjacency. -/
def inverse (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ :=
  Matrix.fromBlocks 0 (prefixInverse n).transpose (prefixInverse n) 0

/-- Exact inverse for every even path size, without any inverse premise. -/
theorem adjacency_mul_inverse (n : ℕ) : adjacency n * inverse n = 1 := by
  rw [adjacency, inverse, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    bidiagonal_mul_prefixInverse]
  have ht := congrArg Matrix.transpose (prefixInverse_mul_bidiagonal n)
  simp only [Matrix.transpose_mul, Matrix.transpose_one] at ht
  rw [ht]
  exact Matrix.fromBlocks_one

theorem inverse_mul_adjacency (n : ℕ) : inverse n * adjacency n = 1 := by
  exact mul_eq_one_comm.mpr (adjacency_mul_inverse n)

/-- Bipartite parity forces every diagonal inverse entry to vanish. -/
theorem inverse_diagonal (n : ℕ) (i : Fin n ⊕ Fin n) : inverse n i i = 0 := by
  cases i <;> rfl

/-- More strongly, every inverse entry within one parity class is zero. -/
theorem inverse_same_parity_left (n : ℕ) (i j : Fin n) :
    inverse n (Sum.inl i) (Sum.inl j) = 0 := rfl

theorem inverse_same_parity_right (n : ℕ) (i j : Fin n) :
    inverse n (Sum.inr i) (Sum.inr j) = 0 := rfl

/-- The block representation is precisely ordinary path adjacency: vertex
`2*i` is joined to `2*j+1` exactly when `i=j` or `i=j+1`. -/
theorem adjacency_cross_entry (n : ℕ) (i j : Fin n) :
    adjacency n (Sum.inl i) (Sum.inr j) =
      if i.val = j.val ∨ i.val = j.val + 1 then 1 else 0 := by
  change (1 : Matrix (Fin n) (Fin n) ℚ) i j + shift n i j = _
  by_cases h : i = j
  · subst j
    simp [shift]
  · have hv : i.val ≠ j.val := fun he => h (Fin.ext he)
    simp [shift, h, hv, eq_comm]

/-- For a path on `4*j` internal vertices, the inverse far corner is `-1`. -/
theorem inverse_far_corner (j : ℕ) (hj : 0 < j) :
    inverse (2 * j) (Sum.inl ⟨0, by omega⟩)
      (Sum.inr ⟨2 * j - 1, by omega⟩) = -1 := by
  change (if 0 ≤ 2 * j - 1 then (-1 : ℚ) ^ (2 * j - 1 - 0) else 0) = -1
  simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  have h : 2 * j - 1 = 2 * (j - 1) + 1 := by omega
  rw [h, pow_add, pow_mul]
  norm_num

/-- Every entry of the explicit inverse lies in `{-1,0,1}` in magnitude. -/
theorem prefixInverse_abs_le_one (n : ℕ) (i j : Fin n) :
    |prefixInverse n i j| ≤ 1 := by
  unfold prefixInverse
  split_ifs <;> simp [abs_pow]

theorem inverse_abs_le_one (n : ℕ) (i j : Fin n ⊕ Fin n) :
    |inverse n i j| ≤ 1 := by
  cases i with
  | inl i =>
    cases j with
    | inl j => norm_num [inverse]
    | inr j => exact prefixInverse_abs_le_one n j i
  | inr i =>
    cases j with
    | inl j => exact prefixInverse_abs_le_one n i j
    | inr j => norm_num [inverse]

/-- Each inverse row has absolute sum at most half the path vertex count.
This gives an induced infinity-norm bound without changing matrix norm
conventions or appealing to a finite-size experiment. -/
theorem inverse_row_abs_sum_le (n : ℕ) (i : Fin n ⊕ Fin n) :
    ∑ j, |inverse n i j| ≤ (n : ℚ) := by
  cases i with
  | inl i =>
    simp only [Fintype.sum_sum_type, inverse, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, abs_zero,
      Finset.sum_const_zero, zero_add, Matrix.transpose_apply]
    calc
      ∑ j : Fin n, |prefixInverse n j i| ≤ ∑ _j : Fin n, (1 : ℚ) :=
        Finset.sum_le_sum (fun j _ => prefixInverse_abs_le_one n j i)
      _ = n := by simp
  | inr i =>
    simp only [Fintype.sum_sum_type, inverse, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, abs_zero,
      Finset.sum_const_zero, add_zero]
    calc
      ∑ j : Fin n, |prefixInverse n i j| ≤ ∑ _j : Fin n, (1 : ℚ) :=
        Finset.sum_le_sum (fun j _ => prefixInverse_abs_le_one n i j)
      _ = n := by simp

/-- The inverse solves every rational right-hand side exactly. -/
theorem inverse_solution (n : ℕ) (b : Fin n ⊕ Fin n → ℚ) :
    adjacency n *ᵥ (inverse n *ᵥ b) = b := by
  rw [Matrix.mulVec_mulVec, adjacency_mul_inverse, Matrix.one_mulVec]

/-- Exact error propagation, for every candidate vector and right-hand side. -/
theorem inverse_residual (n : ℕ) (x b : Fin n ⊕ Fin n → ℚ) :
    inverse n *ᵥ (adjacency n *ᵥ x - b) = x - inverse n *ᵥ b := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, inverse_mul_adjacency,
    Matrix.one_mulVec]

/-- The same explicitly specified path over the real scalars used in the paper. -/
noncomputable def realAdjacency (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  (adjacency n).map (Rat.castHom ℝ)

noncomputable def realInverse (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  (inverse n).map (Rat.castHom ℝ)

theorem realAdjacency_mul_realInverse (n : ℕ) :
    realAdjacency n * realInverse n = 1 := by
  have h := congrArg (fun M => M.map (Rat.castHom ℝ)) (adjacency_mul_inverse n)
  simpa only [realAdjacency, realInverse, Matrix.map_mul,
    Matrix.map_one _ (map_zero _) (map_one _)] using h

theorem realInverse_mul_realAdjacency (n : ℕ) :
    realInverse n * realAdjacency n = 1 := by
  exact mul_eq_one_comm.mpr (realAdjacency_mul_realInverse n)

theorem realInverse_diagonal (n : ℕ) (i : Fin n ⊕ Fin n) :
    realInverse n i i = 0 := by
  simp [realInverse, Matrix.map_apply, inverse_diagonal]

theorem realInverse_far_corner (j : ℕ) (hj : 0 < j) :
    realInverse (2 * j) (Sum.inl ⟨0, by omega⟩)
      (Sum.inr ⟨2 * j - 1, by omega⟩) = -1 := by
  simp [realInverse, Matrix.map_apply, inverse_far_corner j hj]

theorem realInverse_abs_le_one (n : ℕ) (i j : Fin n ⊕ Fin n) :
    |realInverse n i j| ≤ 1 := by
  change |(inverse n i j : ℝ)| ≤ 1
  exact_mod_cast inverse_abs_le_one n i j

open scoped Matrix.Norms.L2Operator

lemma entry_bound_euclidean_norm {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℝ) (hA : ∀ i j, |A i j| ≤ 1) :
    ‖A‖ ≤ Fintype.card d := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hrow (i : d) : ∑ j, (A i j) ^ 2 ≤ (Fintype.card d : ℝ) := by
    calc
      _ ≤ ∑ _j : d, (1 : ℝ) := Finset.sum_le_sum (by
        intro j _
        exact (sq_le_one_iff_abs_le_one _).mpr (hA i j))
      _ = _ := by simp
  have hrowx (i : d) : (∑ j, A i j * x j) ^ 2 ≤
      (Fintype.card d : ℝ) * ∑ j, (x j) ^ 2 := by
    calc
      _ ≤ (∑ j, (A i j) ^ 2) * ∑ j, (x j) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) (fun j => x j)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) (Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hsq : ‖Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) A x‖ ^ 2 ≤
      ((Fintype.card d : ℝ) * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : d, (Fintype.card d : ℝ) * ∑ j, (x j) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact hrowx i
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← EuclideanSpace.real_norm_sq_eq]
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- The Euclidean operator norm is at most the total internal vertex count. -/
theorem realInverse_norm_le (n : ℕ) : ‖realInverse n‖ ≤ (2 * n : ℝ) := by
  have h := entry_bound_euclidean_norm (realInverse n) (realInverse_abs_le_one n)
  simpa [Fintype.card_sum, Fintype.card_fin, two_mul] using h

/-- The path estimate in the paper, in the Euclidean operator norm. -/
theorem realInverse_4j_norm_le (j : ℕ) : ‖realInverse (2 * j)‖ ≤ (4 * j : ℝ) := by
  have h := realInverse_norm_le (2 * j)
  push_cast at h
  nlinarith

/-- Standard linear numbering of the grouped odd/even path vertices. -/
def position {n : ℕ} : Fin n ⊕ Fin n → ℕ
  | Sum.inl i => 2 * i.val
  | Sum.inr i => 2 * i.val + 1

theorem position_lt {n : ℕ} (i : Fin n ⊕ Fin n) : position i < 2 * n := by
  cases i with
  | inl i => simp only [position]; omega
  | inr i => simp only [position]; omega

theorem position_injective (n : ℕ) : Function.Injective (@position n) := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j => congr 1; apply Fin.ext; simp only [position] at h; omega
    | inr j => simp only [position] at h; omega
  | inr i =>
    cases j with
    | inl j => simp only [position] at h; omega
    | inr j => congr 1; apply Fin.ext; simp only [position] at h; omega

/-- Matrix entries equal one precisely for consecutive path positions.
This identifies the block indexing with ordinary path adjacency. -/
theorem adjacency_eq_consecutive (n : ℕ) (i j : Fin n ⊕ Fin n) :
    adjacency n i j =
      if position i + 1 = position j ∨ position j + 1 = position i then 1 else 0 := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change 0 = if 2 * i.val + 1 = 2 * j.val ∨ 2 * j.val + 1 = 2 * i.val then 1 else 0
      have h : ¬ (2 * i.val + 1 = 2 * j.val ∨ 2 * j.val + 1 = 2 * i.val) := by omega
      simp only [h, ↓reduceIte]
    | inr j =>
      rw [adjacency_cross_entry]
      simp only [position]
      have h : (i.val = j.val ∨ i.val = j.val + 1) ↔
          (2 * i.val + 1 = 2 * j.val + 1 ∨ 2 * j.val + 1 + 1 = 2 * i.val) := by omega
      simp only [h]
      rfl
  | inr i =>
    cases j with
    | inl j =>
      change adjacency n (Sum.inl j) (Sum.inr i) = _
      rw [adjacency_cross_entry]
      simp only [position]
      have h : (j.val = i.val ∨ j.val = i.val + 1) ↔
          (2 * i.val + 1 + 1 = 2 * j.val ∨ 2 * j.val + 1 = 2 * i.val + 1) := by omega
      simp only [h]
      rfl
    | inr j =>
      change 0 = if (2 * i.val + 1) + 1 = 2 * j.val + 1 ∨
        (2 * j.val + 1) + 1 = 2 * i.val + 1 then 1 else 0
      have h : ¬ ((2 * i.val + 1) + 1 = 2 * j.val + 1 ∨
        (2 * j.val + 1) + 1 = 2 * i.val + 1) := by omega
      simp only [h, ↓reduceIte]

theorem adjacency_nonsing_inv (n : ℕ) : (adjacency n)⁻¹ = inverse n :=
  Matrix.inv_eq_right_inv (adjacency_mul_inverse n)

theorem realAdjacency_nonsing_inv (n : ℕ) : (realAdjacency n)⁻¹ = realInverse n :=
  Matrix.inv_eq_right_inv (realAdjacency_mul_realInverse n)

/-- The exact all-input, real-valued equation and residual identity. -/
theorem real_inverse_residual (n : ℕ) (x b : Fin n ⊕ Fin n → ℝ) :
    realInverse n *ᵥ (realAdjacency n *ᵥ x - b) = x - realInverse n *ᵥ b := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, realInverse_mul_realAdjacency,
    Matrix.one_mulVec]

/-- All four assertions of the paper's internal-wire inverse estimate. -/
theorem wire_inverse (j : ℕ) (hj : 0 < j) :
    let l : Fin (2 * j) ⊕ Fin (2 * j) := Sum.inl ⟨0, by omega⟩
    let r : Fin (2 * j) ⊕ Fin (2 * j) := Sum.inr ⟨2 * j - 1, by omega⟩
    (realAdjacency (2 * j))⁻¹ l l = 0 ∧
    (realAdjacency (2 * j))⁻¹ r r = 0 ∧
    (realAdjacency (2 * j))⁻¹ l r = -1 ∧
    ‖(realAdjacency (2 * j))⁻¹‖ ≤ (4 * j : ℝ) := by
  dsimp only
  rw [realAdjacency_nonsing_inv]
  exact ⟨realInverse_diagonal _ _, realInverse_diagonal _ _,
    realInverse_far_corner j hj, realInverse_4j_norm_le j⟩

end Maxwell.Logical.Path
