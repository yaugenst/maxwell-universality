import Maxwell.Composition.PhysicalCore
import Maxwell.Composition.DecoratedCells
import Maxwell.Composition.Conditioning

/-! The emitted all-cell scalar material and its exact full-operator
factorization. Material validity holds on every detuning draw. -/
noncomputable section
namespace Maxwell.Composition.PhysicalMaterial
open Maxwell.Spectral Maxwell.Spectral.Lattice
open Maxwell.Composition.PhysicalGram

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
variable (hd : P.spacing.minimumDistance ≤ d)
variable (J : ℕ) (j : Fin J)
local instance : DecidableEq (SourceDecoration.Vertex S precision) := Classical.decEq _

abbrev sigma := Probability.rationalMidpoint (width P ζ hζ) J j.val

def backgroundValue (c : (box P S precision d ζ hζ hζ1).Cell) : ℚ :=
  (PhysicalBackground.material P (box P S precision d ζ hζ hζ1)).value c + 64*sigma P ζ hζ J j

theorem background_bounds (c : (box P S precision d ζ hζ hζ1).Cell) :
    1 ≤ backgroundValue P S precision d ζ hζ hζ1 J j c ∧
      backgroundValue P S precision d ζ hζ hζ1 J j c ≤ 25-P.background.reserve/2 := by
  have hσ := Probability.rationalMidpoint_mem (width P ζ hζ) J j (P.constants.detuningWidth_pos ζ hζ)
  have hw := (P.constants.detuningWidth_bounds ζ hζ).2.2.2
  change width P ζ hζ ≤ P.background.reserve/128 at hw
  have hb := P.background.bounds (siteMod20 (Target.latticeCell c))
  change 1 ≤ P.background.material _ + 64*sigma P ζ hζ J j ∧
    P.background.material _ + 64*sigma P ζ hζ J j ≤ 25-P.background.reserve/2
  change 0 < sigma P ζ hζ J j ∧ sigma P ζ hζ J j < width P ζ hζ at hσ
  constructor <;> linarith

theorem strength_headroom (v : SourceDecoration.Vertex S precision → ℚ)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ P.incrementBound) (i : SourceDecoration.Vertex S precision) :
    0 ≤ v i ∧ 64*v i ≤ P.background.reserve/2 := by
  have hr := P.increment_reserve
  exact ⟨(hv i).1, by linarith [(hv i).2]⟩

def material (v : SourceDecoration.Vertex S precision → ℚ)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ P.incrementBound) :
    ScalarMaterial (box P S precision d ζ hζ hζ1).nx (box P S precision d ζ hζ hζ1).ny
      (box P S precision d ζ hζ hζ1).nz :=
  DecoratedDefectLayout.material S precision P.basis P.basis_injective P.defect d
    (P.chosenBuffer S precision d ζ hζ hζ1) (P.spacing_separates d hd)
    (backgroundValue P S precision d ζ hζ hζ1 J j) v (P.background.reserve/2)
    (by exact div_nonneg P.background.reserve_pos.le (by norm_num))
    (background_bounds P S precision d ζ hζ hζ1 J j) (strength_headroom P S precision v hv)

def matrix (v : SourceDecoration.Vertex S precision → ℚ)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ P.incrementBound) :
    Matrix (box P S precision d ζ hζ hζ1).Edge (box P S precision d ζ hζ hζ1).Edge ℝ :=
  (Target.maxwell (material P S precision d ζ hζ hζ1 hd J j v hv)).map Rat.cast

theorem background_matrix :
    (Target.operator (box P S precision d ζ hζ hζ1)
      (backgroundValue P S precision d ζ hζ hζ1 J j)).map Rat.cast =
        PhysicalBackground.shiftedMatrix P (box P S precision d ζ hζ hζ1) (sigma P ζ hζ J j) := by
  unfold backgroundValue
  rw [Target.operator_uniform_shift]
  ext e f
  simp only [Matrix.map_apply, Matrix.sub_apply, Rat.cast_sub, Matrix.smul_apply, smul_eq_mul,
    Rat.cast_mul, PhysicalBackground.shiftedMatrix, PhysicalBackground.matrix, Target.maxwell]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> norm_num

abbrev realBackground (hm : 0 < S.nnz) (hj : j.val ∉ bad P S precision d ζ hζ hζ1 J) :=
  PhysicalBackground.realEquiv P (box P S precision d ζ hζ hζ1) S.nnz J (width P ζ hζ)
    hm (P.constants.detuningWidth_pos ζ hζ) j hj

theorem operator_factorization (hm : 0 < S.nnz)
    (hj : j.val ∉ bad P S precision d ζ hζ hζ1 J)
    (v : SourceDecoration.Vertex S precision → ℚ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ P.incrementBound)
    (hv0 : ∀ i, v i ≠ 0) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (matrix P S precision d ζ hζ hζ1 hd J j v hv) =
      finitePhysicalOperator (realBackground P S precision d ζ hζ hζ1 J j hm hj)
        ((layout P S precision d ζ hζ hζ1 hd).strengthEquiv v hv0)
        (coordinateRestriction (layout P S precision d ζ hζ hζ1 hd).pick)
        (coordinateExtension (layout P S precision d ζ hζ hζ1 hd).pick) := by
  apply (layout P S precision d ζ hζ hζ1 hd).physical_operator
    (backgroundValue P S precision d ζ hζ hζ1 J j)
    (realBackground P S precision d ζ hζ hζ1 J j hm hj) _ v hv0
  rw [background_matrix, realBackground, PhysicalBackground.realEquiv, ComplexInverse.realEquiv_coe]

theorem core_binding (hm : 0 < S.nnz)
    (hj : j.val ∉ bad P S precision d ζ hζ hζ1 J)
    (v : SourceDecoration.Vertex S precision → ℚ) (hv0 : ∀ i, v i ≠ 0) :
    weightedBirmanSchwinger (realBackground P S precision d ζ hζ hζ1 J j hm hj)
      ((layout P S precision d ζ hζ hζ1 hd).strengthEquiv v hv0)
      (layout P S precision d ζ hζ hζ1 hd).weightEquiv
      (coordinateRestriction (layout P S precision d ζ hζ hζ1 hd).pick)
      (coordinateExtension (layout P S precision d ζ hζ hζ1 hd).pick) =
        PhysicalCore.core P S precision d ζ hζ hζ1 hd hm J j hj v := by
  exact FiniteGram.weighted_core_eq (layout P S precision d ζ hζ hζ1 hd)
    (PhysicalBackground.shiftedMatrix P (box P S precision d ζ hζ hζ1) (sigma P ζ hζ J j))
    (background P S precision d ζ hζ hζ1 hm J j hj)
    (realBackground P S precision d ζ hζ hζ1 J j hm hj)
    (ComplexInverse.complexEquiv_coe _ _) (ComplexInverse.realEquiv_coe _ _) v hv0

end Maxwell.Composition.PhysicalMaterial
