import Maxwell.SchurBound
import Maxwell.Composition.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! A matrix of local operator norms controls the actual complete Euclidean
block operator. Row and column estimates do not acquire a defect-count factor. -/

noncomputable section

namespace Maxwell.Composition

open scoped BigOperators

variable {ι κ : Type*}

def blockCoordinate (x : EuclideanSpace ℝ (ι × κ)) (i : ι) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 fun j => x (i, j)

@[simp] theorem blockCoordinate_add (x y : EuclideanSpace ℝ (ι × κ)) (i : ι) :
    blockCoordinate (x + y) i = blockCoordinate x i + blockCoordinate y i := by
  ext j
  rfl

@[simp] theorem blockCoordinate_smul (a : ℝ) (x : EuclideanSpace ℝ (ι × κ)) (i : ι) :
    blockCoordinate (a • x) i = a • blockCoordinate x i := by
  ext j
  rfl

variable [Fintype ι] [Fintype κ]

theorem euclidean_norm_sq_blocks (x : EuclideanSpace ℝ (ι × κ)) :
    ‖x‖ ^ 2 = ∑ i, ‖blockCoordinate x i‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, blockCoordinate, Fintype.sum_prod_type]

def interactionLinear (A : ι → ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ (ι × κ) →ₗ[ℝ] EuclideanSpace ℝ (ι × κ) where
  toFun x := WithLp.toLp 2 fun ij => (∑ j, A ij.1 j (blockCoordinate x j)) ij.2
  map_add' x y := by
    ext ij
    simp [Finset.sum_add_distrib]
  map_smul' a x := by
    ext ij
    simp [Finset.mul_sum]

def interactionOperator
    (A : ι → ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ) :=
  (interactionLinear A).toContinuousLinearMap

theorem interaction_block_action
    (A : ι → ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (x : EuclideanSpace ℝ (ι × κ)) (i : ι) :
    blockCoordinate (interactionOperator A x) i = ∑ j, A i j (blockCoordinate x j) := by
  ext k
  rfl

/-- This is the block-operator Schur estimate used for the complete
interaction tail. All blocks may be dense; no local coordinate dimension
or number of occupied defects is inserted into the bound. -/
theorem interaction_operator_norm_le
    (A : ι → ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ R) :
    ‖interactionOperator A‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg x))).mp
  rw [euclidean_norm_sq_blocks, mul_pow, euclidean_norm_sq_blocks]
  have hpoint : ∀ i,
      ‖blockCoordinate (interactionOperator A x) i‖ ≤
        ∑ j, ‖A i j‖ * ‖blockCoordinate x j‖ := by
    intro i
    rw [interaction_block_action]
    exact (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => (A i j).le_opNorm (blockCoordinate x j))
  calc
    ∑ i, ‖blockCoordinate (interactionOperator A x) i‖ ^ 2 ≤
        ∑ i, (∑ j, ‖A i j‖ * ‖blockCoordinate x j‖) ^ 2 := by
      exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hpoint i) 2
    _ ≤ R ^ 2 * ∑ j, ‖blockCoordinate x j‖ ^ 2 := by
      exact Maxwell.matrix_schur_square_bound (fun i j => ‖A i j‖) R hR
        (by simpa only [abs_norm] using hrow)
        (by simpa only [abs_norm] using hcol)
        (fun j => ‖blockCoordinate x j‖)

/-- The full non-nearest interaction operator over an arbitrary finite
occupied subset of the cubic lattice has a dimension-free quadratic tail.
The hypotheses concern the actual individual local blocks; the conclusion
is the norm of their assembled Euclidean operator. -/
theorem lattice_interaction_operator_norm_le
    (A : ι → ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (position : ι → Lattice3) (hinj : Function.Injective position)
    (C ζ : ℝ) (hC : 0 ≤ C) (hζ : 0 ≤ ζ) (hhalf : ζ ≤ 1 / 2)
    (hnear : ∀ i j, latticeDistance (position j - position i) < 2 → A i j = 0)
    (hdecay : ∀ i j, ‖A i j‖ ≤ C * latticeWeight ζ (position j - position i)) :
    ‖interactionOperator A‖ ≤ 256 * C * ζ ^ 2 := by
  have hR : 0 ≤ C * (256 * ζ ^ 2) := by positivity
  have hrow : ∀ i, ∑ j, ‖A i j‖ ≤ C * (256 * ζ ^ 2) := by
    intro i
    apply occupied_far_row_bound (fun j => position j - position i)
      (fun a b h => hinj (sub_left_inj.mp h)) (fun j => ‖A i j‖)
      C ζ hC hζ hhalf
    · intro j hj
      rw [hnear i j hj, norm_zero]
    · exact hdecay i
  have hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C * (256 * ζ ^ 2) := by
    intro j
    apply occupied_far_row_bound (fun i => position j - position i)
      (fun a b h => hinj (sub_right_inj.mp h)) (fun i => ‖A i j‖)
      C ζ hC hζ hhalf
    · intro i hi
      rw [hnear i j hi, norm_zero]
    · intro i
      exact hdecay i j
  calc
    ‖interactionOperator A‖ ≤ C * (256 * ζ ^ 2) :=
      interaction_operator_norm_le A _ hR hrow hcol
    _ = 256 * C * ζ ^ 2 := by ring

end Maxwell.Composition
