import Maxwell.Composition.SourceDefectBounds
import Maxwell.Composition.Weights
import Maxwell.Composition.Complex
import Maxwell.Green.BoundaryStrip

/-! The finite background Gram operator on the complete actual defect union.
Its coordinate restriction, square-root weights and infinite embedding are
constructed from the finite scalar-cell layout. -/
noncomputable section
namespace Maxwell.Composition.FiniteGram
open Maxwell.Spectral Maxwell.Spectral.Lattice
open scoped BigOperators InnerProduct

variable {B : Target.Box} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable {blocks : ι → Finset B.Cell} (layout : DefectLayout (κ := κ) blocks)

/-- All physical defect coordinates, in their actual finite layout order. -/
def unionEmbedding : (ι × κ) ↪ Edge :=
  ⟨fun ij => Target.latticeEdge B (layout.pick ij),
    (Target.latticeEdge B).injective.comp layout.injective⟩

def restriction : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ (ι × κ) :=
  (Target.sequenceRestriction (unionEmbedding layout)).comp (Target.edgeExtension B)

@[simp] theorem restriction_apply (x : EuclideanSpace ℂ B.Edge) (ij : ι × κ) :
    restriction layout x ij = x (layout.pick ij) := by
  change Target.sequenceRestriction (unionEmbedding layout) (Target.edgeExtension B x) ij = _
  rw [Target.sequenceRestriction_apply]
  exact Target.sequenceExtensionLinear_at (Target.latticeEdge B) x (layout.pick ij)

theorem restriction_norm_le : ‖restriction layout‖ ≤ 1 := by
  calc
    _ ≤ ‖Target.sequenceRestriction (unionEmbedding layout)‖ * ‖Target.edgeExtension B‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (Target.sequenceRestriction_norm_le _)
      (Target.edgeExtension_norm_le _) (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num

theorem restriction_adjoint :
    (restriction layout).adjoint = (Target.edgeRestriction B).comp
      (Target.sequenceExtension (unionEmbedding layout)).toContinuousLinearMap := by
  rw [restriction, ContinuousLinearMap.adjoint_comp]
  change (Target.edgeExtension B).adjoint.comp
    ((Target.sequenceExtension (unionEmbedding layout)).toContinuousLinearMap.adjoint.adjoint) = _
  rw [ContinuousLinearMap.adjoint_adjoint]
  rfl

theorem restriction_latticeRestriction :
    (restriction layout).comp (Target.edgeRestriction B) =
      Target.sequenceRestriction (unionEmbedding layout) := by
  ext x ij
  rw [ContinuousLinearMap.comp_apply, restriction_apply]
  change Target.sequenceRestriction (Target.latticeEdge B) x (layout.pick ij) = _
  rw [Target.sequenceRestriction_apply, Target.sequenceRestriction_apply]
  rfl

def sqrtWeight : EuclideanSpace ℂ (ι × κ) →L[ℂ] EuclideanSpace ℂ (ι × κ) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.diagonal fun ij => (layout.sqrtWeight ij : ℂ))

@[simp] theorem sqrtWeight_apply (x : EuclideanSpace ℂ (ι × κ)) (ij : ι × κ) :
    sqrtWeight layout x ij = (layout.sqrtWeight ij : ℂ) * x ij := by
  change (Matrix.diagonal fun ij => (layout.sqrtWeight ij : ℂ)).mulVec x ij = _
  exact Matrix.mulVec_diagonal _ _ _

theorem sqrtWeight_norm_le : ‖sqrtWeight layout‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, sqrtWeight_apply, norm_mul]
  apply Finset.sum_le_sum
  intro ij _
  have hw : ‖(layout.sqrtWeight ij : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ layout.sqrtWeight ij from Real.sqrt_nonneg _)]
    exact (layout.sqrtWeight_bounds ij).2
  have hm := mul_le_mul_of_nonneg_right hw (norm_nonneg (x ij))
  simpa only [one_mul] using pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hm 2

theorem sqrtWeight_selfAdjoint : (sqrtWeight layout).adjoint = sqrtWeight layout := by
  have hs : IsSelfAdjoint (sqrtWeight layout) := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    apply Finset.sum_congr rfl
    intro ij _
    change y ij * star (sqrtWeight layout x ij) = sqrtWeight layout y ij * star (x ij)
    rw [sqrtWeight_apply, sqrtWeight_apply]
    simp only [map_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [← ContinuousLinearMap.star_eq_adjoint, hs.star_eq]

/-- Weighted finite background compression on all defect coordinates. -/
def finite (A : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge) :
    EuclideanSpace ℂ (ι × κ) →L[ℂ] EuclideanSpace ℂ (ι × κ) :=
  (sqrtWeight layout).comp ((restriction layout).comp
    (A.comp ((restriction layout).adjoint.comp (sqrtWeight layout))))

/-- The same coordinates and same weights, using the genuine infinite inverse. -/
def infinite (H : Field →L[ℂ] Field) :
    EuclideanSpace ℂ (ι × κ) →L[ℂ] EuclideanSpace ℂ (ι × κ) :=
  (sqrtWeight layout).comp ((Target.sequenceRestriction (unionEmbedding layout)).comp
    (H.comp ((Target.sequenceExtension (unionEmbedding layout)).toContinuousLinearMap.comp
      (sqrtWeight layout))))

/-- Whole-union finite-boundary error. No number of defects or local-stencil
size appears in the norm bound. All geometric support is actual PEC support. -/
theorem finite_infinite_error [Nonempty (ι × κ)]
    (material : ScalarMaterial B.nx B.ny B.nz) (m : Site → ℝ)
    (hcell : ∀ c : B.Cell, m (Target.latticeCell c) = (material.value c : ℝ))
    (M : ℝ) (hM : 0 ≤ M) (hm : ∀ e, |Target.latticeEdgeAverage m e| ≤ M)
    (A : EuclideanSpace ℂ B.Edge ≃L[ℂ] EuclideanSpace ℂ B.Edge)
    (H : Field ≃L[ℂ] Field) (σ : ℂ)
    (hA : (A : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge) =
      Green.pecMaxwellOperator material - σ • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ B.Edge))
    (hH : (H : Field →L[ℂ] Field) = electricOperator (Target.latticeEdgeAverage m) M hM hm)
    (g τ J L μ buffer : ℝ) (hg : 0 < g) (hμ : 0 ≤ μ) (hbuffer : 0 ≤ buffer)
    (hmargin : ∀ ij k, buffer ≤ ((unionEmbedding layout ij).2 k : ℝ) ∧
      ((unionEmbedding layout ij).2 k : ℝ) + buffer ≤ (Green.boxSide B k : ℝ))
    (hinv : ‖(H.symm : Field →L[ℂ] Field)‖ ≤ 1 / g)
    (hfinite : ‖(A.symm : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge)‖ ≤ L)
    (hnorm : ‖(H : Field →L[ℂ] Field)‖ ≤ J)
    (hτ : ‖σ‖ ≤ τ) (hσ : ‖σ‖ ≤ g / 4)
    (hsmall : 16 * (Real.exp (2 * μ) - 1) ≤ g / 4) :
    ‖finite layout (A.symm : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge) -
      infinite layout (H.symm : Field →L[ℂ] Field)‖ ≤
      2 * τ / g ^ 2 + (4 * J * L / g) * Real.exp (-μ * buffer) := by
  have h := Green.finite_background_error_of_coordinate_margin material m hcell M hM hm
    A H σ hA hH (unionEmbedding layout) (restriction layout) (restriction_norm_le layout)
    g τ J L μ buffer hg hμ hbuffer hmargin hinv hfinite hnorm hτ hσ hsmall
  rw [← restriction_adjoint, restriction_latticeRestriction] at h
  let T := (restriction layout).comp
    ((A.symm : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge).comp (restriction layout).adjoint) -
    (Target.sequenceRestriction (unionEmbedding layout)).comp
      ((H.symm : Field →L[ℂ] Field).comp
        (Target.sequenceExtension (unionEmbedding layout)).toContinuousLinearMap)
  have heq : finite layout (A.symm : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge) -
      infinite layout (H.symm : Field →L[ℂ] Field) =
      (sqrtWeight layout).comp (T.comp (sqrtWeight layout)) := by
    ext x
    simp only [finite, infinite, T, ContinuousLinearMap.comp_apply, sub_apply, map_sub]
  rw [heq]
  exact (Green.compression_norm_le _ _ _ (sqrtWeight_norm_le layout)
    (sqrtWeight_norm_le layout)).trans h

end Maxwell.Composition.FiniteGram
