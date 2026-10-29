import Maxwell.Composition.PhysicalMaterial

/-! Full retained-edge Maxwell inversion and conditioning from the actual
constructed weighted core, including the untouched finite background. -/
noncomputable section
set_option synthInstance.maxSize 1024
namespace Maxwell.Composition.PhysicalWoodbury
open Maxwell.Composition.PhysicalGram
open Maxwell.Composition.PhysicalMaterial

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
variable (hd : P.spacing.minimumDistance ≤ d) (hm : 0 < S.nnz)
variable (J : ℕ) (j : Fin J) (hj : j.val ∉ bad P S precision d ζ hζ hζ1 J)
variable (v : SourceDecoration.Vertex S precision → ℚ)
variable (hv : ∀ i, 0 ≤ v i ∧ v i ≤ P.incrementBound) (hv0 : ∀ i, v i ≠ 0)
local instance : DecidableEq (SourceDecoration.Vertex S precision) := Classical.decEq _

abbrev Coordinates := EuclideanSpace ℝ
  (SourceDecoration.Vertex S precision × Fin (Maxwell.Defect.ScalarDefect.edges P.defect).card)

variable (M : Coordinates P S precision ≃L[ℝ] Coordinates P S precision)
variable (hM : (M : Coordinates P S precision →L[ℝ] Coordinates P S precision) =
  PhysicalCore.core P S precision d ζ hζ hζ1 hd hm J j hj v)

def fullEquiv : EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge ≃L[ℝ]
    EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge :=
  physicalEquivOfWeighted (realBackground P S precision d ζ hζ hζ1 J j hm hj)
    ((layout P S precision d ζ hζ hζ1 hd).strengthEquiv v hv0)
    (layout P S precision d ζ hζ hζ1 hd).weightEquiv M
    (coordinateRestriction (layout P S precision d ζ hζ hζ1 hd).pick)
    (coordinateExtension (layout P S precision d ζ hζ hζ1 hd).pick)
    (hM.trans (PhysicalMaterial.core_binding P S precision d ζ hζ hζ1 hd J j hm hj v hv0).symm)

theorem fullEquiv_operator :
    (fullEquiv P S precision d ζ hζ hζ1 hd hm J j hj v hv0 M hM :
      EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge →L[ℝ]
        EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (PhysicalMaterial.matrix P S precision d ζ hζ hζ1 hd J j v hv) := by
  rw [fullEquiv, physicalEquivOfWeighted_operator]
  exact (PhysicalMaterial.operator_factorization P S precision d ζ hζ hζ1 hd J j hm hj v hv hv0).symm

def inverseBudget (QM : ℝ) : ℝ :=
  let L := (P.constants.backgroundInverseBudget ζ hζ S.nnz (Fintype.card (box P S precision d ζ hζ hζ1).Edge) : ℝ)
  L + L^2*QM

theorem fullEquiv_inverse_bound (QM : ℝ)
    (hQM : ‖(M.symm : Coordinates P S precision →L[ℝ] Coordinates P S precision)‖ ≤ QM) :
    ‖((fullEquiv P S precision d ζ hζ hζ1 hd hm J j hj v hv0 M hM).symm :
      EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge →L[ℝ]
        EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge)‖ ≤
      inverseBudget P S precision d ζ hζ hζ1 QM := by
  apply physicalEquivOfWeighted_inverse_norm_le
  · rw [P.constants.backgroundInverseBudget_cast]
    exact PhysicalBackground.real_inverse_bound P _ S.nnz J (width P ζ hζ) hm
      (P.constants.detuningWidth_pos ζ hζ) j hj
  · exact (layout P S precision d ζ hζ hζ1 hd).weightEquiv_norm_le
  · exact coordinateRestriction_norm_le _ (layout P S precision d ζ hζ hζ1 hd).injective
  · exact coordinateExtension_norm_le _ (layout P S precision d ζ hζ hζ1 hd).injective
  · exact hQM

include hm hj hv0 hM in
/-- Conditioning is for the full literal emitted Maxwell matrix. -/
theorem full_conditioning (QM : ℝ)
    (hQM : ‖(M.symm : Coordinates P S precision →L[ℝ] Coordinates P S precision)‖ ≤ QM) :
    IsUnit (PhysicalMaterial.matrix P S precision d ζ hζ hζ1 hd J j v hv) ∧
      condition₂ (PhysicalMaterial.matrix P S precision d ζ hζ hζ1 hd J j v hv) ≤
        16*inverseBudget P S precision d ζ hζ hζ1 QM := by
  have hop := fullEquiv_operator P S precision d ζ hζ hζ1 hd hm J j hj v hv hv0 M hM
  constructor
  · exact matrix_isUnit_of_operator_equiv _ _ hop
  · apply matrix_condition_of_operator_equiv _ _ hop 16 _ (by norm_num)
    · rw [hop]
      exact Target.maxwell_real_toEuclideanCLM_norm_le (material P S precision d ζ hζ hζ1 hd J j v hv)
    · exact fullEquiv_inverse_bound P S precision d ζ hζ hζ1 hd hm J j hj v hv0 M hM QM hQM

end Maxwell.Composition.PhysicalWoodbury
