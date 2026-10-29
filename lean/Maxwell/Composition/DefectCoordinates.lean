import Maxwell.ScalarAssembly
import Maxwell.Composition.BlockModes
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Actual coordinate restriction and zero extension for disjoint finite
defect coordinates, and their scalar-cell diagonal factorization. -/

noncomputable section

namespace Maxwell.Composition

open scoped BigOperators InnerProduct

section Coordinates

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def coordinateRestriction (pick : κ → ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun j => x (pick j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem coordinateRestriction_apply (pick : κ → ι)
    (x : EuclideanSpace ℝ ι) (j : κ) : coordinateRestriction pick x j = x (pick j) := rfl

def coordinateExtension (pick : κ → ι) :
    EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι :=
  (coordinateRestriction pick).adjoint

omit [DecidableEq κ] in
theorem coordinateExtension_apply (pick : κ → ι) (x : EuclideanSpace ℝ κ) (i : ι) :
    coordinateExtension pick x i = ∑ j, if pick j = i then x j else 0 := by
  have h := ContinuousLinearMap.adjoint_inner_right (coordinateRestriction pick)
    (EuclideanSpace.single i 1) x
  simpa [coordinateExtension, PiLp.inner_apply, eq_comm] using h.symm

omit [DecidableEq κ] in
theorem coordinateRestriction_norm_le (pick : κ → ι) (hinj : Function.Injective pick) :
    ‖coordinateRestriction pick‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, coordinateRestriction_apply]
  calc
    ∑ j, x (pick j) ^ 2 = ∑ i ∈ Finset.univ.image pick, x i ^ 2 := by
      rw [Finset.sum_image (fun i _ j _ h => hinj h)]
    _ ≤ ∑ i, x i ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)

omit [DecidableEq κ] in
theorem coordinateExtension_norm_le (pick : κ → ι) (hinj : Function.Injective pick) :
    ‖coordinateExtension pick‖ ≤ 1 := by
  unfold coordinateExtension
  rw [LinearIsometryEquiv.norm_map]
  exact coordinateRestriction_norm_le pick hinj

@[simp] theorem coordinateRestriction_extension (pick : κ → ι)
    (hinj : Function.Injective pick) (x : EuclideanSpace ℝ κ) :
    coordinateRestriction pick (coordinateExtension pick x) = x := by
  ext j
  rw [coordinateRestriction_apply, coordinateExtension_apply]
  simp [hinj.eq_iff]

omit [DecidableEq κ] in
theorem coordinateExtension_diagonal_restriction (pick : κ → ι)
    (v : κ → ℝ) :
    (coordinateExtension pick).comp ((blockDiagonal v).comp (coordinateRestriction pick)) =
      blockDiagonal (fun i => ∑ j, if pick j = i then v j else 0) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, coordinateExtension_apply, blockDiagonal_apply,
    coordinateRestriction_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · rw [h]
  · simp

end Coordinates

section ScalarDefects

variable {B : Target.Box} {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The concrete layout contract says exactly which coordinates are touched
by each cell block. Injectivity of `pick` then asserts disjoint touched-edge
supports; the spectral properties are not part of this layout data. -/
structure DefectLayout (blocks : ι → Finset B.Cell) where
  pick : ι × κ → B.Edge
  injective : Function.Injective pick
  support : ∀ i e, 0 < Target.defectWeight (blocks i) e ↔ ∃ j, pick (i, j) = e

def DefectLayout.weight {blocks : ι → Finset B.Cell} (layout : DefectLayout (κ := κ) blocks)
    (ij : ι × κ) : ℚ := Target.defectWeight (blocks ij.1) (layout.pick ij)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem DefectLayout.weight_bounds {blocks : ι → Finset B.Cell}
    (layout : DefectLayout (κ := κ) blocks) (ij : ι × κ) :
    1 / 4 ≤ layout.weight ij ∧ layout.weight ij ≤ 1 := by
  have hp : 0 < layout.weight ij := by
    apply (layout.support ij.1 (layout.pick ij)).mpr
    exact ⟨ij.2, rfl⟩
  exact ⟨Target.defectWeight_quarter_le _ _ hp, (Target.defectWeight_bounds _ _).2⟩

omit [DecidableEq ι] [DecidableEq κ] in
theorem DefectLayout.mass_sum {blocks : ι → Finset B.Cell}
    (layout : DefectLayout (κ := κ) blocks) (v : ι → ℚ) (e : B.Edge) :
    (∑ ij : ι × κ, if layout.pick ij = e then v ij.1 * layout.weight ij else 0) =
      ∑ i, v i * Target.defectWeight (blocks i) e := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases he : ∃ j, layout.pick (i, j) = e
  · obtain ⟨j, hj⟩ := he
    rw [Finset.sum_eq_single j]
    · simp [hj, DefectLayout.weight]
    · intro k _ hkj
      have hk : layout.pick (i, k) ≠ e := by
        intro hk
        have heq := layout.injective (hk.trans hj.symm)
        exact hkj (Prod.mk.inj heq).2
      simp [hk]
    · simp
  · have hz : Target.defectWeight (blocks i) e = 0 := by
      have hn := (Target.defectWeight_bounds (blocks i) e).1
      have hp : ¬ 0 < Target.defectWeight (blocks i) e := by
        simpa only [layout.support i e] using he
      linarith
    have hne : ∀ j, layout.pick (i, j) ≠ e := by simpa using he
    simp [hne, hz]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Complete scalar-cell diagonal mass factorization through the actual
disjoint coordinate restriction, with all untouched edges still present. -/
theorem DefectLayout.mass_factorization {blocks : ι → Finset B.Cell}
    (layout : DefectLayout (κ := κ) blocks) (v : ι → ℚ) :
    (coordinateExtension layout.pick).comp
      ((blockDiagonal (fun ij => ((v ij.1 * layout.weight ij : ℚ) : ℝ))).comp
        (coordinateRestriction layout.pick)) =
      blockDiagonal (fun e => ((∑ i, v i * Target.defectWeight (blocks i) e : ℚ) : ℝ)) := by
  rw [coordinateExtension_diagonal_restriction]
  congr 1
  funext e
  have h := layout.mass_sum v e
  simpa only [Rat.cast_sum, apply_ite, Rat.cast_zero] using
    congrArg (fun z : ℚ => (z : ℝ)) h

omit [DecidableEq ι] [DecidableEq κ] in
/-- The exact rational cell update, cast to the actual real Euclidean
operator, has the required restriction/weighted-diagonal/insertion form. -/
theorem DefectLayout.operator_factorization {blocks : ι → Finset B.Cell}
    (layout : DefectLayout (κ := κ) blocks) (background : B.Cell → ℚ) (v : ι → ℚ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := B.Edge)
      ((Target.operator B (Target.assembledMaterial background blocks v)).map Rat.cast) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := B.Edge)
        ((Target.operator B background).map Rat.cast) -
      (coordinateExtension layout.pick).comp
        ((blockDiagonal (fun ij => ((v ij.1 * layout.weight ij : ℚ) : ℝ))).comp
          (coordinateRestriction layout.pick)) := by
  rw [layout.mass_factorization]
  have hmat : (Target.operator B (Target.assembledMaterial background blocks v)).map
      (fun z : ℚ => (z : ℝ)) =
      (Target.operator B background).map (fun z : ℚ => (z : ℝ)) -
        Matrix.diagonal (fun e => ((∑ i, v i * Target.defectWeight (blocks i) e : ℚ) : ℝ)) := by
    rw [Target.assembledMaterial_operator]
    ext e f
    by_cases hef : e = f <;> simp [hef]
  rw [hmat, map_sub]
  congr 1
  ext x e
  change (Matrix.diagonal
    (fun e => ((∑ i, v i * Target.defectWeight (blocks i) e : ℚ) : ℝ))).mulVec
      (WithLp.ofLp x) e = _
  simp [Matrix.mulVec_diagonal, blockDiagonal_apply]

end ScalarDefects

end Maxwell.Composition
