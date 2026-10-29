import Maxwell.Defect.FiniteCompression
import Maxwell.Defect.RealCompression
import Maxwell.Defect.WeightEnclosure
import Maxwell.Defect.CompressedNumerator

/-! The finite defect source map into the actual complex lattice Hilbert
space, with exact real-compression and source-adjoint identities. -/

namespace Maxwell.Defect
open Spectral Spectral.Lattice
variable {n : ℕ}

noncomputable def complexSqrtWeightOperator (W : Fin n → ℚ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
    (Matrix.diagonal (fun i => (Real.sqrt (W i : ℝ) : ℂ)))

@[simp] theorem complexSqrtWeightOperator_apply (W : Fin n → ℚ)
    (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    complexSqrtWeightOperator W x i = (Real.sqrt (W i : ℝ) : ℂ) * x i := by
  change (Matrix.diagonal (fun j => (Real.sqrt (W j : ℝ) : ℂ))).mulVec x i = _
  exact Matrix.mulVec_diagonal _ _ _

@[simp] theorem sqrtWeightOperator_apply (W : Fin n → ℚ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    sqrtWeightOperator W x i = Real.sqrt (W i : ℝ) * x i := by
  change (Matrix.diagonal (fun j => Real.sqrt (W j : ℝ))).mulVec x i = _
  exact Matrix.mulVec_diagonal _ _ _

theorem complexSqrtWeightOperator_embedding (W : Fin n → ℚ)
    (x : EuclideanSpace ℝ (Fin n)) :
    complexSqrtWeightOperator W (realCoordinateEmbedding x) =
      realCoordinateEmbedding (sqrtWeightOperator W x) := by
  ext i
  simp

theorem complexSqrtWeightOperator_part (W : Fin n → ℚ)
    (x : EuclideanSpace ℂ (Fin n)) :
    realCoordinatePart (complexSqrtWeightOperator W x) =
      sqrtWeightOperator W (realCoordinatePart x) := by
  ext i
  simp

theorem complexSqrtWeightOperator_selfAdjoint (W : Fin n → ℚ) :
    IsSelfAdjoint (complexSqrtWeightOperator W) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  change y i * star (complexSqrtWeightOperator W x i) =
    complexSqrtWeightOperator W y i * star (x i)
  rw [complexSqrtWeightOperator_apply, complexSqrtWeightOperator_apply]
  simp only [map_mul, Complex.star_def, Complex.conj_ofReal]
  ring

/-- The actual weighted finite source map used by both the diagonal
Birman--Schwinger block and its translated off-diagonal Green blocks. -/
noncomputable def defectInjection (edges : Fin n ↪ Edge) (W : Fin n → ℚ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] Field :=
  (Target.sequenceExtension edges).toContinuousLinearMap.comp (complexSqrtWeightOperator W)

@[simp] theorem defectInjection_apply_at (edges : Fin n ↪ Edge) (W : Fin n → ℚ)
    (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    defectInjection edges W x (edges i) = (Real.sqrt (W i : ℝ) : ℂ) * x i := by
  change Target.sequenceExtensionLinear edges (complexSqrtWeightOperator W x) (edges i) = _
  rw [Target.sequenceExtensionLinear_at, complexSqrtWeightOperator_apply]

theorem defectInjection_apply_of_notMem (edges : Fin n ↪ Edge) (W : Fin n → ℚ)
    (x : EuclideanSpace ℂ (Fin n)) (e : Edge) (he : e ∉ Set.range edges) :
    defectInjection edges W x e = 0 := by
  change Target.sequenceExtensionLinear edges (complexSqrtWeightOperator W x) e = _
  rw [Target.sequenceExtensionLinear_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact ite_eq_right (fun h => he ⟨i, h.symm⟩)

theorem defectInjection_adjoint (edges : Fin n ↪ Edge) (W : Fin n → ℚ) :
    (defectInjection edges W).adjoint =
      (complexSqrtWeightOperator W).comp (Target.sequenceRestriction edges) := by
  rw [defectInjection, ContinuousLinearMap.adjoint_comp]
  have hs := complexSqrtWeightOperator_selfAdjoint W
  rw [← ContinuousLinearMap.star_eq_adjoint, hs.star_eq]
  rfl

@[simp] theorem defectInjection_adjoint_apply (edges : Fin n ↪ Edge) (W : Fin n → ℚ)
    (x : Field) (i : Fin n) :
    (defectInjection edges W).adjoint x i = (Real.sqrt (W i : ℝ) : ℂ) * x (edges i) := by
  rw [defectInjection_adjoint]
  simp [Target.sequenceRestriction_apply]

theorem defectInjection_compression (edges : Fin n ↪ Edge) (W : Fin n → ℚ)
    (R : Field →L[ℂ] Field) :
    sourceCompression (defectInjection edges W) R =
      complexSqrtWeightOperator W * FiniteStencil.compressionOperator edges R *
        complexSqrtWeightOperator W := by
  rw [sourceCompression_apply, defectInjection_adjoint]
  rfl

theorem realPartOperator_weighted (W : Fin n → ℚ)
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    realPartOperator (complexSqrtWeightOperator W * R * complexSqrtWeightOperator W) =
      sqrtWeightOperator W * realPartOperator R * sqrtWeightOperator W := by
  apply ContinuousLinearMap.ext
  intro x
  change realCoordinatePart (complexSqrtWeightOperator W
    (R (complexSqrtWeightOperator W (realCoordinateEmbedding x)))) = _
  rw [complexSqrtWeightOperator_embedding, complexSqrtWeightOperator_part]
  rfl

theorem defectInjection_real_compression (edges : Fin n ↪ Edge) (W : Fin n → ℚ)
    (R : Field →L[ℂ] Field) :
    realPartOperator (sourceCompression (defectInjection edges W) R) =
      sqrtWeightOperator W * realPartOperator (FiniteStencil.compressionOperator edges R) *
        sqrtWeightOperator W := by
  rw [defectInjection_compression, realPartOperator_weighted]

theorem weighted_real_coordinates (W : Fin n → ℚ)
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hR : ∀ x : EuclideanSpace ℝ (Fin n),
      realCoordinateEmbedding (realPartOperator R x) = R (realCoordinateEmbedding x))
    (x : EuclideanSpace ℝ (Fin n)) :
    realCoordinateEmbedding
      (realPartOperator (complexSqrtWeightOperator W * R * complexSqrtWeightOperator W) x) =
      (complexSqrtWeightOperator W * R * complexSqrtWeightOperator W)
        (realCoordinateEmbedding x) := by
  rw [realPartOperator_weighted]
  change realCoordinateEmbedding
    (sqrtWeightOperator W (realPartOperator R (sqrtWeightOperator W x))) = _
  rw [← complexSqrtWeightOperator_embedding, hR, ← complexSqrtWeightOperator_embedding]
  rfl

theorem sourceCompression_selfAdjoint {U H : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : U →L[ℂ] H) (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) :
    IsSelfAdjoint (sourceCompression K R) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, sourceCompression_apply,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ← ContinuousLinearMap.star_eq_adjoint, hR.star_eq]
  rfl

theorem complexSqrtWeightOperator_norm_apply_le (W : Fin n → ℚ)
    (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖complexSqrtWeightOperator W x‖ ≤ ‖x‖ := by
  have hs : ‖complexSqrtWeightOperator W x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    rw [complexSqrtWeightOperator_apply, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by exact_mod_cast hW i)]
    exact mul_le_of_le_one_left (sq_nonneg _) (by exact_mod_cast hW1 i)
  nlinarith [norm_nonneg (complexSqrtWeightOperator W x), norm_nonneg x]

theorem defectInjection_norm_apply_le (edges : Fin n ↪ Edge) (W : Fin n → ℚ)
    (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1)
    (x : EuclideanSpace ℂ (Fin n)) : ‖defectInjection edges W x‖ ≤ ‖x‖ := by
  change ‖Target.sequenceExtension edges (complexSqrtWeightOperator W x)‖ ≤ ‖x‖
  rw [(Target.sequenceExtension edges).norm_map]
  exact complexSqrtWeightOperator_norm_apply_le W hW hW1 x

end Maxwell.Defect
