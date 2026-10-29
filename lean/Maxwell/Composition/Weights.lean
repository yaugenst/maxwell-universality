import Maxwell.Composition.DefectCoordinates
import Maxwell.Composition.SourceIdentity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The weighted defect coordinate changes are constructed from the actual
four-cell material weights. The inverse square-root weight bound is two,
uniformly in the number and shape of disjoint scalar defect blocks. -/

noncomputable section

namespace Maxwell.Composition

section DiagonalEquivalence

variable {ι : Type*} [Fintype ι]

def diagonalEquiv (v : ι → ℝ) (hv : ∀ i, v i ≠ 0) :
    EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι :=
  ContinuousLinearEquiv.equivOfInverse' (blockDiagonal v) (blockDiagonal (fun i => (v i)⁻¹))
    (by ext x i; simp [blockDiagonal_apply, hv])
    (by ext x i; simp [blockDiagonal_apply, hv])

@[simp] theorem diagonalEquiv_operator (v : ι → ℝ) (hv : ∀ i, v i ≠ 0) :
    (diagonalEquiv v hv : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      blockDiagonal v := rfl

@[simp] theorem diagonalEquiv_inverse (v : ι → ℝ) (hv : ∀ i, v i ≠ 0) :
    ((diagonalEquiv v hv).symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      blockDiagonal (fun i => (v i)⁻¹) := rfl

end DiagonalEquivalence

section PhysicalWeights

variable {B : Target.Box} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {blocks : ι → Finset B.Cell}

def DefectLayout.sqrtWeight (layout : DefectLayout (κ := κ) blocks) (ij : ι × κ) : ℝ :=
  Real.sqrt (layout.weight ij : ℝ)

omit [Fintype ι] [Fintype κ] in
theorem DefectLayout.sqrtWeight_bounds (layout : DefectLayout (κ := κ) blocks)
    (ij : ι × κ) : 1 / 2 ≤ layout.sqrtWeight ij ∧ layout.sqrtWeight ij ≤ 1 := by
  have hw : (1 / 4 : ℝ) ≤ (layout.weight ij : ℝ) ∧ (layout.weight ij : ℝ) ≤ 1 := by
    constructor
    · have h : (((1 / 4 : ℚ) : ℝ)) ≤ (layout.weight ij : ℝ) :=
        Rat.cast_le.mpr (layout.weight_bounds ij).1
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
    · exact_mod_cast (layout.weight_bounds ij).2
  have hn : 0 ≤ (layout.weight ij : ℝ) := by linarith
  have hs := Real.sq_sqrt hn
  have hpos := Real.sqrt_nonneg (layout.weight ij : ℝ)
  dsimp [DefectLayout.sqrtWeight]
  constructor <;> nlinarith

omit [Fintype ι] [Fintype κ] in
theorem DefectLayout.sqrtWeight_ne_zero (layout : DefectLayout (κ := κ) blocks)
    (ij : ι × κ) : layout.sqrtWeight ij ≠ 0 := by
  have h := (layout.sqrtWeight_bounds ij).1
  linarith

def DefectLayout.weightEquiv (layout : DefectLayout (κ := κ) blocks) :
    EuclideanSpace ℝ (ι × κ) ≃L[ℝ] EuclideanSpace ℝ (ι × κ) :=
  diagonalEquiv layout.sqrtWeight layout.sqrtWeight_ne_zero

theorem DefectLayout.weightEquiv_norm_le (layout : DefectLayout (κ := κ) blocks) :
    ‖(layout.weightEquiv : EuclideanSpace ℝ (ι × κ) →L[ℝ]
      EuclideanSpace ℝ (ι × κ))‖ ≤ 1 := by
  apply blockDiagonal_norm_le layout.sqrtWeight 1 zero_le_one
  intro ij
  rw [abs_of_nonneg (show 0 ≤ layout.sqrtWeight ij from Real.sqrt_nonneg _)]
  exact (layout.sqrtWeight_bounds ij).2

theorem DefectLayout.weightEquiv_inverse_norm_le (layout : DefectLayout (κ := κ) blocks) :
    ‖(layout.weightEquiv.symm : EuclideanSpace ℝ (ι × κ) →L[ℝ]
      EuclideanSpace ℝ (ι × κ))‖ ≤ 2 := by
  apply blockDiagonal_norm_le (fun ij => (layout.sqrtWeight ij)⁻¹) 2 (by norm_num)
  intro ij
  rw [abs_inv, abs_of_nonneg (show 0 ≤ layout.sqrtWeight ij from Real.sqrt_nonneg _)]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2)
    (layout.sqrtWeight_bounds ij).1
  simpa only [one_div, inv_div, inv_one, mul_one, inv_inv] using h

theorem DefectLayout.weightEquiv_square (layout : DefectLayout (κ := κ) blocks) :
    (layout.weightEquiv : EuclideanSpace ℝ (ι × κ) →L[ℝ]
      EuclideanSpace ℝ (ι × κ)).comp (layout.weightEquiv :
        EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ)) =
      blockDiagonal (fun ij => (layout.weight ij : ℝ)) := by
  ext x ij
  change layout.sqrtWeight ij * (layout.sqrtWeight ij * x ij) =
    (layout.weight ij : ℝ) * x ij
  have hw : 0 ≤ (layout.weight ij : ℝ) := by
    apply Rat.cast_nonneg.mpr
    exact le_trans (by norm_num) (layout.weight_bounds ij).1
  rw [← mul_assoc, ← pow_two, DefectLayout.sqrtWeight, Real.sq_sqrt hw]

def DefectLayout.strengthEquiv (layout : DefectLayout (κ := κ) blocks)
    (v : ι → ℚ) (hv : ∀ i, v i ≠ 0) :
    EuclideanSpace ℝ (ι × κ) ≃L[ℝ] EuclideanSpace ℝ (ι × κ) :=
  diagonalEquiv (fun ij => ((v ij.1 * layout.weight ij : ℚ) : ℝ)) (by
    intro ij
    have hw : layout.weight ij ≠ 0 := by
      have h := (layout.weight_bounds ij).1
      linarith
    exact_mod_cast mul_ne_zero (hv ij.1) hw)

/-- The scalar-cell Maxwell operator is exactly the physical operator used
in the weighted Schur and Woodbury proofs, with actual coordinate maps. -/
theorem DefectLayout.physical_operator {blocks : ι → Finset B.Cell}
    (layout : DefectLayout (κ := κ) blocks) (background : B.Cell → ℚ)
    (K : EuclideanSpace ℝ B.Edge ≃L[ℝ] EuclideanSpace ℝ B.Edge)
    (hK : (K : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := B.Edge)
        ((Target.operator B background).map Rat.cast))
    (v : ι → ℚ) (hv : ∀ i, v i ≠ 0) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := B.Edge)
      ((Target.operator B (Target.assembledMaterial background blocks v)).map Rat.cast) =
      finitePhysicalOperator K (layout.strengthEquiv v hv)
        (coordinateRestriction layout.pick) (coordinateExtension layout.pick) := by
  classical
  rw [layout.operator_factorization]
  rw [finitePhysicalOperator, hK]
  rfl

end PhysicalWeights

end Maxwell.Composition
