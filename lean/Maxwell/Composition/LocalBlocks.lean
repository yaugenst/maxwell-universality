import Maxwell.Composition.Interactions

/-! A finite direct sum of local invertible blocks, with the genuine
Euclidean norm. Uniform local inverse estimates remain independent of the
number of defects. -/

noncomputable section

namespace Maxwell.Composition

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def diagonalBlocksLinear
    (A : ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ (ι × κ) →ₗ[ℝ] EuclideanSpace ℝ (ι × κ) where
  toFun x := WithLp.toLp 2 fun ij => A ij.1 (blockCoordinate x ij.1) ij.2
  map_add' x y := by ext ij; simp
  map_smul' a x := by ext ij; simp

def diagonalBlocks (A : ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ) :=
  (diagonalBlocksLinear A).toContinuousLinearMap

@[simp] theorem diagonalBlocks_apply
    (A : ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (x : EuclideanSpace ℝ (ι × κ)) (i : ι) (j : κ) :
    diagonalBlocks A x (i, j) = A i (blockCoordinate x i) j := rfl

@[simp] theorem diagonalBlocks_coordinate
    (A : ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (x : EuclideanSpace ℝ (ι × κ)) (i : ι) :
    blockCoordinate (diagonalBlocks A x) i = A i (blockCoordinate x i) := by
  ext j
  rfl

theorem diagonalBlocks_norm_le
    (A : ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (R : ℝ) (hR : 0 ≤ R) (hA : ∀ i, ‖A i‖ ≤ R) :
    ‖diagonalBlocks A‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg x))).mp
  rw [euclidean_norm_sq_blocks, mul_pow, euclidean_norm_sq_blocks, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [diagonalBlocks_coordinate, ← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact ((A i).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))

theorem diagonalBlocks_inverse_left
    (A : ι → EuclideanSpace ℝ κ ≃L[ℝ] EuclideanSpace ℝ κ)
    (x : EuclideanSpace ℝ (ι × κ)) :
    diagonalBlocks (fun i => (A i : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ))
      (diagonalBlocks (fun i => ((A i).symm : EuclideanSpace ℝ κ →L[ℝ]
        EuclideanSpace ℝ κ)) x) = x := by
  ext ij
  rcases ij with ⟨i, j⟩
  simp only [diagonalBlocks_apply, diagonalBlocks_coordinate,
    ContinuousLinearEquiv.coe_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem diagonalBlocks_inverse_right
    (A : ι → EuclideanSpace ℝ κ ≃L[ℝ] EuclideanSpace ℝ κ)
    (x : EuclideanSpace ℝ (ι × κ)) :
    diagonalBlocks (fun i => ((A i).symm : EuclideanSpace ℝ κ →L[ℝ]
      EuclideanSpace ℝ κ))
      (diagonalBlocks (fun i => (A i : EuclideanSpace ℝ κ →L[ℝ]
        EuclideanSpace ℝ κ)) x) = x := by
  ext ij
  rcases ij with ⟨i, j⟩
  simp only [diagonalBlocks_apply, diagonalBlocks_coordinate,
    ContinuousLinearEquiv.coe_apply, ContinuousLinearEquiv.symm_apply_apply]
  rfl

def diagonalBlockEquiv (A : ι → EuclideanSpace ℝ κ ≃L[ℝ] EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ (ι × κ) ≃L[ℝ] EuclideanSpace ℝ (ι × κ) :=
  ContinuousLinearEquiv.equivOfInverse'
    (diagonalBlocks (fun i => (A i : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)))
    (diagonalBlocks (fun i => ((A i).symm : EuclideanSpace ℝ κ →L[ℝ]
      EuclideanSpace ℝ κ)))
    (ContinuousLinearMap.ext (diagonalBlocks_inverse_left A))
    (ContinuousLinearMap.ext (diagonalBlocks_inverse_right A))

theorem diagonalBlockEquiv_inverse_norm_le
    (A : ι → EuclideanSpace ℝ κ ≃L[ℝ] EuclideanSpace ℝ κ)
    (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ i, ‖((A i).symm : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)‖ ≤ R) :
    ‖((diagonalBlockEquiv A).symm : EuclideanSpace ℝ (ι × κ) →L[ℝ]
      EuclideanSpace ℝ (ι × κ))‖ ≤ R :=
  diagonalBlocks_norm_le
    (fun i => ((A i).symm : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)) R hR hA

end Maxwell.Composition
