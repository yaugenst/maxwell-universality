import Maxwell.Composition.FiniteGram

/-! Exact passage from the physical complex compression to the real
weighted Birman--Schwinger coordinates used by the decoder. -/
noncomputable section
namespace Maxwell.Composition.FiniteGram
open scoped BigOperators

section RealOperator
variable {ν : Type*} [Fintype ν]

def realPart : EuclideanSpace ℂ ν →L[ℝ] EuclideanSpace ℝ ν :=
  LinearMap.toContinuousLinearMap
    { toFun := euclideanRealPart
      map_add' := by intros; ext i; simp [euclideanRealPart]
      map_smul' := by intros; ext i; simp [euclideanRealPart] }

def complexLift : EuclideanSpace ℝ ν →L[ℝ] EuclideanSpace ℂ ν :=
  LinearMap.toContinuousLinearMap
    { toFun := euclideanComplexLift
      map_add' := by intros; ext i; simp [euclideanComplexLift]
      map_smul' := by intros; ext i; simp [euclideanComplexLift] }

def realOperator (T : EuclideanSpace ℂ ν →L[ℂ] EuclideanSpace ℂ ν) :
    EuclideanSpace ℝ ν →L[ℝ] EuclideanSpace ℝ ν :=
  realPart.comp ((T.restrictScalars ℝ).comp complexLift)

@[simp] theorem realOperator_apply (T : EuclideanSpace ℂ ν →L[ℂ] EuclideanSpace ℂ ν)
    (x : EuclideanSpace ℝ ν) : realOperator T x = euclideanRealPart (T (euclideanComplexLift x)) := rfl

theorem realOperator_norm_le (T : EuclideanSpace ℂ ν →L[ℂ] EuclideanSpace ℂ ν) :
    ‖realOperator T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖euclideanRealPart (T (euclideanComplexLift x))‖ ≤ _
  exact (euclideanRealPart_norm_le _).trans (by simpa using T.le_opNorm (euclideanComplexLift x))

@[simp] theorem realOperator_sub (T U : EuclideanSpace ℂ ν →L[ℂ] EuclideanSpace ℂ ν) :
    realOperator (T - U) = realOperator T - realOperator U := by
  ext x i
  simp only [realOperator_apply, sub_apply, euclideanRealPart_apply, PiLp.sub_apply, Complex.sub_re]

theorem inverse_realPart [DecidableEq ν] (M : Matrix ν ν ℝ)
    (A : EuclideanSpace ℂ ν ≃L[ℂ] EuclideanSpace ℂ ν)
    (K : EuclideanSpace ℝ ν ≃L[ℝ] EuclideanSpace ℝ ν)
    (hA : (A : EuclideanSpace ℂ ν →L[ℂ] EuclideanSpace ℂ ν) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (M.map fun a => (a : ℂ)))
    (hK : (K : EuclideanSpace ℝ ν →L[ℝ] EuclideanSpace ℝ ν) = Matrix.toEuclideanCLM (𝕜 := ℝ) M)
    (y : EuclideanSpace ℂ ν) :
    euclideanRealPart (A.symm y) = K.symm (euclideanRealPart y) := by
  apply K.injective
  have h := realPart_matrix_action M (A.symm y)
  rw [← hA, ← hK] at h
  simpa using h.symm
end RealOperator

variable {B : Target.Box} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable {blocks : ι → Finset B.Cell} (layout : DefectLayout (κ := κ) blocks)

@[simp] theorem restriction_realPart (y : EuclideanSpace ℂ B.Edge) :
    euclideanRealPart (restriction layout y) =
      coordinateRestriction layout.pick (euclideanRealPart y) := by
  ext ij
  simp [restriction_apply]

@[simp] theorem sqrtWeight_realPart (y : EuclideanSpace ℂ (ι × κ)) :
    euclideanRealPart (sqrtWeight layout y) = layout.weightEquiv (euclideanRealPart y) := by
  ext ij
  rw [euclideanRealPart_apply, sqrtWeight_apply]
  change ((layout.sqrtWeight ij : ℂ) * y ij).re = layout.sqrtWeight ij * (y ij).re
  simp

@[simp] theorem restriction_adjoint_apply (x : EuclideanSpace ℂ (ι × κ)) (e : B.Edge) :
    (restriction layout).adjoint x e = ∑ ij, if layout.pick ij = e then x ij else 0 := by
  have h := ContinuousLinearMap.adjoint_inner_right (restriction layout)
    (EuclideanSpace.single e 1) x
  simpa [PiLp.inner_apply, restriction_apply, eq_comm] using h.symm

@[simp] theorem restriction_adjoint_realPart (y : EuclideanSpace ℂ (ι × κ)) :
    euclideanRealPart ((restriction layout).adjoint y) =
      coordinateExtension layout.pick (euclideanRealPart y) := by
  ext e
  rw [euclideanRealPart_apply, restriction_adjoint_apply, coordinateExtension_apply]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro ij _
  split_ifs <;> rfl

/-- The real extraction is exactly the Q/W-weighted finite Gram term, not
a separately specified approximation. -/
theorem real_finite_eq (M : Matrix B.Edge B.Edge ℝ)
    (A : EuclideanSpace ℂ B.Edge ≃L[ℂ] EuclideanSpace ℂ B.Edge)
    (K : EuclideanSpace ℝ B.Edge ≃L[ℝ] EuclideanSpace ℝ B.Edge)
    (hA : (A : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (M.map fun a => (a : ℂ)))
    (hK : (K : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge) = Matrix.toEuclideanCLM (𝕜 := ℝ) M) :
    realOperator (finite layout (A.symm : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge)) =
      (layout.weightEquiv : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ)).comp
        ((coordinateRestriction layout.pick).comp
          ((K.symm : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge).comp
            ((coordinateExtension layout.pick).comp
              (layout.weightEquiv : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ))))) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [realOperator_apply, finite, ContinuousLinearMap.comp_apply,
    sqrtWeight_realPart, restriction_realPart]
  change layout.weightEquiv ((coordinateRestriction layout.pick)
    (euclideanRealPart (A.symm ((restriction layout).adjoint (sqrtWeight layout (euclideanComplexLift x)))))) = _
  rw [inverse_realPart M A K hA hK, restriction_adjoint_realPart, sqrtWeight_realPart,
    euclideanRealPart_lift]
  rfl

/-- Any whole-union complex compression error controls the actual real
Gram error with the identical bound. -/
theorem real_gram_error (A : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge)
    (H : Maxwell.Spectral.Lattice.Field →L[ℂ] Maxwell.Spectral.Lattice.Field)
    (δ : ℝ) (hδ : ‖finite layout A - infinite layout H‖ ≤ δ) :
    ‖realOperator (finite layout A) - realOperator (infinite layout H)‖ ≤ δ := by
  rw [← realOperator_sub]
  exact (realOperator_norm_le _).trans hδ

end Maxwell.Composition.FiniteGram
