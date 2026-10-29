import Maxwell.Logical.Path

/-! Chronological numbering of the exact internal-wire inverse. -/

namespace Maxwell.Logical.PathOrder

open Matrix
open scoped Matrix

/-- Explicit parity interleaving: grouped even and odd vertices are sent to
positions `2*i` and `2*i+1`, with division by two as the inverse. -/
def orderEquiv (j : ℕ) : Fin (2 * j) ⊕ Fin (2 * j) ≃ Fin (4 * j) where
  toFun i := ⟨Path.position i, by have h := Path.position_lt i; omega⟩
  invFun k := if k.val % 2 = 0 then
    Sum.inl ⟨k.val / 2, by omega⟩ else Sum.inr ⟨k.val / 2, by omega⟩
  left_inv i := by
    cases i with
    | inl i =>
      simp only [Path.position, Nat.mul_mod_right, ↓reduceIte]
      congr 1
      apply Fin.ext
      dsimp only
      omega
    | inr i =>
      have hm : (2 * i.val + 1) % 2 ≠ 0 := by omega
      simp only [Path.position, hm, ↓reduceIte]
      congr 1
      apply Fin.ext
      dsimp only
      omega
  right_inv k := by
    apply Fin.ext
    dsimp only
    split_ifs with h
    · simp only [Path.position]
      omega
    · simp only [Path.position]
      omega

@[simp] theorem orderEquiv_val (j : ℕ) (i : Fin (2 * j) ⊕ Fin (2 * j)) :
    (orderEquiv j i).val = Path.position i := rfl

@[simp] theorem position_orderEquiv_symm (j : ℕ) (i : Fin (4 * j)) :
    Path.position ((orderEquiv j).symm i) = i.val := by
  exact congrArg Fin.val ((orderEquiv j).apply_symm_apply i)

/-- Ordinary path adjacency on the chronological internal vertices. -/
noncomputable def adjacency (j : ℕ) : Matrix (Fin (4 * j)) (Fin (4 * j)) ℝ :=
  (Path.realAdjacency (2 * j)).submatrix (orderEquiv j).symm (orderEquiv j).symm

/-- The transported, explicitly specified inverse. -/
noncomputable def inverse (j : ℕ) : Matrix (Fin (4 * j)) (Fin (4 * j)) ℝ :=
  (Path.realInverse (2 * j)).submatrix (orderEquiv j).symm (orderEquiv j).symm

theorem adjacency_eq_consecutive (j : ℕ) (a b : Fin (4 * j)) :
    adjacency j a b = if a.val + 1 = b.val ∨ b.val + 1 = a.val then 1 else 0 := by
  simp only [adjacency, Matrix.submatrix_apply, Path.realAdjacency, Matrix.map_apply,
    Path.adjacency_eq_consecutive, position_orderEquiv_symm]
  split_ifs <;> norm_num

theorem adjacency_mul_inverse (j : ℕ) : adjacency j * inverse j = 1 := by
  rw [adjacency, inverse, Matrix.submatrix_mul_equiv,
    Path.realAdjacency_mul_realInverse, Matrix.submatrix_one_equiv]

theorem inverse_mul_adjacency (j : ℕ) : inverse j * adjacency j = 1 := by
  exact mul_eq_one_comm.mpr (adjacency_mul_inverse j)

theorem adjacency_nonsing_inv (j : ℕ) : (adjacency j)⁻¹ = inverse j :=
  Matrix.inv_eq_right_inv (adjacency_mul_inverse j)

@[simp] theorem inverse_diagonal (j : ℕ) (a : Fin (4 * j)) : inverse j a a = 0 :=
  Path.realInverse_diagonal _ _

theorem inverse_symmetric (j : ℕ) (a b : Fin (4 * j)) :
    inverse j a b = inverse j b a := by
  change Path.realInverse (2 * j) ((orderEquiv j).symm a) ((orderEquiv j).symm b) =
    Path.realInverse (2 * j) ((orderEquiv j).symm b) ((orderEquiv j).symm a)
  cases (orderEquiv j).symm a <;> cases (orderEquiv j).symm b <;> rfl

theorem inverse_abs_le_one (j : ℕ) (a b : Fin (4 * j)) : |inverse j a b| ≤ 1 :=
  Path.realInverse_abs_le_one _ _ _

/-- The first and last internal vertices, defined whenever the wire is nonempty. -/
def first (j : ℕ) (hj : 0 < j) : Fin (4 * j) := ⟨0, by omega⟩
def last (j : ℕ) (hj : 0 < j) : Fin (4 * j) := ⟨4 * j - 1, by omega⟩

@[simp] theorem first_val (j : ℕ) (hj : 0 < j) : (first j hj).val = 0 := rfl
@[simp] theorem last_val (j : ℕ) (hj : 0 < j) : (last j hj).val = 4 * j - 1 := rfl

@[simp] theorem orderEquiv_symm_first (j : ℕ) (hj : 0 < j) :
    (orderEquiv j).symm (first j hj) = Sum.inl ⟨0, by omega⟩ := by
  apply (orderEquiv j).injective
  apply Fin.ext
  simp [Path.position]

@[simp] theorem orderEquiv_symm_last (j : ℕ) (hj : 0 < j) :
    (orderEquiv j).symm (last j hj) = Sum.inr ⟨2 * j - 1, by omega⟩ := by
  apply (orderEquiv j).injective
  apply Fin.ext
  simp only [Equiv.apply_symm_apply, last_val, orderEquiv_val, Path.position]
  omega

@[simp] theorem inverse_first_first (j : ℕ) (hj : 0 < j) :
    inverse j (first j hj) (first j hj) = 0 := inverse_diagonal _ _

@[simp] theorem inverse_last_last (j : ℕ) (hj : 0 < j) :
    inverse j (last j hj) (last j hj) = 0 := inverse_diagonal _ _

@[simp] theorem inverse_first_last (j : ℕ) (hj : 0 < j) :
    inverse j (first j hj) (last j hj) = -1 := by
  simp only [inverse, Matrix.submatrix_apply, orderEquiv_symm_first, orderEquiv_symm_last]
  exact Path.realInverse_far_corner j hj

@[simp] theorem inverse_last_first (j : ℕ) (hj : 0 < j) :
    inverse j (last j hj) (first j hj) = -1 := by
  rw [inverse_symmetric, inverse_first_last]

/-- Both absolute row and column sums are bounded by half the internal size. -/
theorem inverse_row_abs_sum_le (j : ℕ) (a : Fin (4 * j)) :
    ∑ b, |inverse j a b| ≤ (2 * j : ℝ) := by
  have h := Path.inverse_row_abs_sum_le (2 * j) ((orderEquiv j).symm a)
  have hr : (∑ b, |Path.realInverse (2 * j) ((orderEquiv j).symm a) b|) ≤
      (2 * j : ℝ) := by
    change (∑ b, |(Path.inverse (2 * j) ((orderEquiv j).symm a) b : ℝ)|) ≤ _
    exact_mod_cast h
  unfold inverse
  simp only [Matrix.submatrix_apply]
  have hs := (orderEquiv j).symm.sum_comp
    (fun b => |Path.realInverse (2 * j) ((orderEquiv j).symm a) b|)
  exact hs.le.trans hr

theorem inverse_col_abs_sum_le (j : ℕ) (b : Fin (4 * j)) :
    ∑ a, |inverse j a b| ≤ (2 * j : ℝ) := by
  simpa only [inverse_symmetric j] using inverse_row_abs_sum_le j b

open scoped Matrix.Norms.L2Operator

theorem inverse_norm_le (j : ℕ) : ‖inverse j‖ ≤ (4 * j : ℝ) := by
  have h := Path.entry_bound_euclidean_norm (inverse j) (inverse_abs_le_one j)
  simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] using h

end Maxwell.Logical.PathOrder
