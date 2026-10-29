import Maxwell.Composition.PhysicalSource
import Maxwell.Composition.SourceRational

/-! Whole-source error for the exact rational source emitted by the
construction. The local-mode and output-grid errors are both charged. -/
noncomputable section
namespace Maxwell.Composition.PhysicalSource
open Maxwell.Composition.PhysicalGram
open Maxwell.Composition.PhysicalMaterial
open Maxwell.Defect
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
variable (hd : P.spacing.minimumDistance ≤ d) (J : ℕ) (j : Fin J)
local instance : DecidableEq (SourceDecoration.Vertex S precision) := Classical.decEq _

theorem shared_weight (i : Sites S precision) (k : Local P) :
    (layout P S precision d ζ hζ hζ1 hd).weight (i,k) = ScalarDefect.coordinateWeight P.defect k :=
  DecoratedDefectLayout.shared_weight S precision P.basis P.basis_injective P.defect d
    (P.chosenBuffer S precision d ζ hζ hζ1) (P.spacing_separates d hd) (i,k)

theorem weightedMode_eq : P.weightedMode =
    weightedLocalMode (ScalarDefect.coordinateWeight P.defect) P.mode := by
  ext k
  change (Matrix.mulVec (Matrix.diagonal (fun i => Real.sqrt (ScalarDefect.coordinateWeight P.defect i : ℝ)))
    (WithLp.ofLp P.mode)) k = Real.sqrt (ScalarDefect.coordinateWeight P.defect k : ℝ) * P.mode k
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal]

def exactLogicalSource : EuclideanSpace ℝ (Sites S precision) :=
  realVector (SourceRational.decorated S precision)

theorem exactLogicalSource_eq : exactLogicalSource S precision =
    sumLeftInjection (κ := SourceIncidence.E S precision) (SourceSubdivision.source S precision) :=
  SourceRational.decorated_vector S precision

theorem exactLogicalSource_norm : ‖exactLogicalSource S precision‖ =
    ‖SourceSubdivision.source S precision‖ := by
  rw [exactLogicalSource_eq, sumLeftInjection_norm_apply]

theorem background_norm (hm : 0 < S.nnz)
    (hj : j.val ∉ bad P S precision d ζ hζ hζ1 J) :
    ‖(realBackground P S precision d ζ hζ hζ1 J j hm hj :
      EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge →L[ℝ]
        EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge)‖ ≤ 16 := by
  let M : ScalarMaterial (box P S precision d ζ hζ hζ1).nx
      (box P S precision d ζ hζ hζ1).ny (box P S precision d ζ hζ hζ1).nz :=
    { value := backgroundValue P S precision d ζ hζ hζ1 J j
      bounds := fun c => ⟨(background_bounds P S precision d ζ hζ hζ1 J j c).1, by
        have := (background_bounds P S precision d ζ hζ hζ1 J j c).2
        have := P.background.reserve_pos
        linarith⟩ }
  have h := Target.maxwell_real_toEuclideanCLM_norm_le M
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
    ((Target.operator _ (backgroundValue P S precision d ζ hζ hζ1 J j)).map Rat.cast)‖ ≤ 16 at h
  rw [background_matrix] at h
  exact h

def emitted (α ε L : ℚ) (hα : 0 < α) (hε : 0 < ε) (hL : 0 < L)
    (q : Local P → ℚ) : (box P S precision d ζ hζ hζ1).Edge → ℚ :=
  rounded P S precision d ζ hζ hζ1 hd J j
    (Realization.PhysicalConstants.sourceBudget α ε L
      (Fintype.card (box P S precision d ζ hζ hζ1).Edge))
    (Realization.PhysicalConstants.sourceBudget_pos α ε L _ hα hε hL)
    α q (SourceRational.decorated S precision)

theorem emitted_rounding_error (α ε L : ℚ) (hα : 0 < α) (hε : 0 < ε) (hL : 0 < L)
    (q : Local P → ℚ) (hb : S.source ≠ 0) :
    ‖realVector (emitted P S precision d ζ hζ hζ1 hd J j α ε L hα hε hL q) -
      realVector (unrounded P S precision d ζ hζ hζ1 hd J j α q
        (SourceRational.decorated S precision))‖ ≤
      (α : ℝ) * ε * ‖exactLogicalSource S precision‖ / (32768 * L) := by
  apply source_rounding_budget _ _ Finset.univ (α : ℝ) (ε : ℝ)
    ‖exactLogicalSource S precision‖ (L : ℝ)
    (by exact_mod_cast hα.le) (by exact_mod_cast hε.le)
    (by rw [exactLogicalSource_norm]; exact (SourceSubdivision.source_norm_bounds S hb precision).1)
    (by exact_mod_cast hL) (by simp)
  intro e _
  have he := rounded_coordinate_error P S precision d ζ hζ hζ1 hd J j
    (Realization.PhysicalConstants.sourceBudget α ε L
      (Fintype.card (box P S precision d ζ hζ hζ1).Edge))
    (Realization.PhysicalConstants.sourceBudget_pos α ε L _ hα hε hL)
    α q (SourceRational.decorated S precision) e
  change |(emitted P S precision d ζ hζ hζ1 hd J j α ε L hα hε hL q e : ℝ) -
    (unrounded P S precision d ζ hζ hζ1 hd J j α q (SourceRational.decorated S precision) e : ℝ)| ≤ _
  apply he.trans
  simp only [Realization.PhysicalConstants.sourceBudget, Rat.cast_div, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_max, Rat.cast_one, Rat.cast_natCast, Finset.card_univ]
  have hαR : (0 : ℝ) < α := by exact_mod_cast hα
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hp : 0 ≤ (α : ℝ) * ε /
      (32768 * L * max 1 (Fintype.card (box P S precision d ζ hζ hζ1).Edge : ℝ)) := by positivity
  linarith

theorem emitted_source_error (hm : 0 < S.nnz)
    (hj : j.val ∉ bad P S precision d ζ hζ hζ1 J)
    (α ε L : ℚ) (hα : 0 < α) (hε : 0 < ε) (hL : 0 < L)
    (q : Local P → ℚ) (hb : S.source ≠ 0)
    (hrow : 16 ≤ P.rowBound)
    (hq : ‖realVector q - P.weightedMode‖ ≤
      (1/4 : ℝ) * ε / (32768 * P.rowBound * L)) :
    ‖realVector (emitted P S precision d ζ hζ hζ1 hd J j α ε L hα hε hL q) -
      localIdealSource (realBackground P S precision d ζ hζ hζ1 J j hm hj)
        (layout P S precision d ζ hζ hζ1 hd).weightEquiv
        (coordinateExtension (layout P S precision d ζ hζ hζ1 hd).pick)
        (blockInjection P.mode ((α : ℝ) • exactLogicalSource S precision))‖ ≤
      (α : ℝ) * ε * ‖exactLogicalSource S precision‖ / (8192 * L) := by
  let K : EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge ≃L[ℝ]
      EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge :=
    realBackground P S precision d ζ hζ hζ1 J j hm hj
  let lay := layout P S precision d ζ hζ hζ1 hd
  have hround := emitted_rounding_error P S precision d ζ hζ hζ1 hd J j α ε L hα hε hL q hb
  rw [unrounded_cast P S precision d ζ hζ hζ1 hd J j hm hj] at hround
  have hcal := modeSource_emitted_budget
    (E := EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge)
    (ι := Sites S precision) (κ := Local P)
    (α : ℝ) (ε : ℝ) ‖exactLogicalSource S precision‖
    (P.rowBound : ℝ) (L : ℝ) (1/4 : ℝ)
    (K : EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge →L[ℝ]
      EuclideanSpace ℝ (box P S precision d ζ hζ hζ1).Edge)
    (coordinateExtension lay.pick) lay.inverseWeight (realVector q) P.weightedMode
    (exactLogicalSource S precision)
    (realVector (emitted P S precision d ζ hζ hζ1 hd J j α ε L hα hε hL q))
    (by exact_mod_cast hα.le) (by exact_mod_cast hε.le)
    (by exact_mod_cast P.rowBound_pos) (by exact_mod_cast hL) (by norm_num)
    ((background_norm P S precision d ζ hζ hζ1 J j hm hj).trans (by exact_mod_cast hrow))
    (coordinateExtension_norm_le lay.pick lay.injective)
    (by convert lay.inverseWeight_norm_le using 1; norm_num)
    le_rfl hq hround
  rw [weightedMode_eq P, lay.shared_source (ScalarDefect.coordinateWeight P.defect)
    (shared_weight P S precision d ζ hζ hζ1 hd) P.mode (exactLogicalSource S precision) (α : ℝ) K] at hcal
  exact emitted_source_budget_weaken (α : ℝ) (ε : ℝ) ‖exactLogicalSource S precision‖ (L : ℝ)
    _ _ (by exact_mod_cast hα.le) (by exact_mod_cast hε.le) (norm_nonneg _)
    (by exact_mod_cast hL) hcal

end Maxwell.Composition.PhysicalSource
