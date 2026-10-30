import Maxwell.Continuum.ParameterSourceResources
import Maxwell.Continuum.WellInteractionLattice

/-! Actual decorated centers on the fixed placement lattice, translated
by one even integer vector into the selected PEC box. -/

noncomputable section
namespace Maxwell.Continuum.Parameters
open Maxwell.Composition PeriodicBand EffectiveMass Auxiliary CellGauge Bloch
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

theorem placementDiagonal_bounds (j : Fin 3) :
    0 ≤ placementDiagonal j ∧ placementDiagonal j ≤ (2 : ℤ)^53 := by
  fin_cases j <;> norm_num [placementDiagonal]

theorem sourcePlacedSite_bound (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (v : SourceDecoration.Vertex S (SelectedInput.input p S hm).precision) (j : Fin 3) :
    0 ≤ (placementMatrix.mulVec (SourceDecoration.site S (SelectedInput.input p S hm).precision v)) j ∧
    (placementMatrix.mulVec (SourceDecoration.site S (SelectedInput.input p S hm).precision v)) j ≤
      ((sourceInput p S hm).span j : ℤ) := by
  have hv := sourceSite_coordinate S (SelectedInput.input p S hm).precision v j
  have hB := placementDiagonal_bounds j
  simp only [placementMatrix, Matrix.mulVec_diagonal]
  refine ⟨mul_nonneg hB.1 hv.1, ?_⟩
  have hmul := mul_le_mul hB.2 hv.2 hv.1 (by positivity : (0 : ℤ) ≤ 2^53)
  apply hmul.trans_eq
  change (2 : ℤ)^53*(258*PhysicalParameters.routingSide S (SelectedInput.input p S hm).precision : ℕ) =
    (2^54*129*PhysicalParameters.routingSide S (SelectedInput.input p S hm).precision : ℕ)
  push_cast
  ring

def margin (L t : ℕ) : ℕ := L+L*t+8
def translationCell (L t : ℕ) : ℕ := (margin L t+1)/2

theorem translationCell_margin (L t : ℕ) :
    margin L t ≤ 2*translationCell L t ∧ 2*translationCell L t ≤ margin L t+1 := by
  unfold translationCell
  omega

def sourceCell (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (k : ℕ)
    (v : SourceDecoration.Vertex S (SelectedInput.input p S hm).precision) : Bloch.Alias :=
  let I := sourceInput p S hm
  fun j => (translationCell (stageLength k) (stageBuffer I MasterConstants.exponent k) : ℤ)+
    placementCell (stageLength k) (stageSpacing I MasterConstants.exponent k)
      (SourceDecoration.site S (SelectedInput.input p S hm).precision v) j

def sourceBox (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (k : ℕ) : Fin 3 → ℕ :=
  let I := sourceInput p S hm
  fun j => stageSpan I MasterConstants.exponent k j+stageLength k+
    stageLength k*stageBuffer I MasterConstants.exponent k+4

theorem sourceBox_side (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (k : ℕ) (j : Fin 3) :
    2*sourceBox p S hm k j = boxSide (stageSpan (sourceInput p S hm) MasterConstants.exponent k)
      (stageLength k) (stageBuffer (sourceInput p S hm) MasterConstants.exponent k) j := rfl

theorem sourceCell_margin (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (k : ℕ) (v : SourceDecoration.Vertex S (SelectedInput.input p S hm).precision) (j : Fin 3) :
    let I := sourceInput p S hm
    let M := margin (stageLength k) (stageBuffer I MasterConstants.exponent k)
    (M : ℤ) ≤ 2*sourceCell p S hm k v j ∧
    2*sourceCell p S hm k v j+(M : ℤ) ≤ 2*(sourceBox p S hm k j : ℤ) := by
  let I := sourceInput p S hm
  let L := stageLength k
  let d := stageSpacing I MasterConstants.exponent k
  let t := stageBuffer I MasterConstants.exponent k
  have hv := sourcePlacedSite_bound p S hm v j
  have hshift := translationCell_margin L t
  have hshiftZ : (margin L t : ℤ) ≤ 2*(translationCell L t : ℤ) ∧
      2*(translationCell L t : ℤ) ≤ (margin L t : ℤ)+1 := by exact_mod_cast hshift
  have hLp : 0 < L := stageLength_pos k
  have hdp : 0 < d := selectedSpacing_pos _ _ _ _ _ _
  have hsp : 0 < I.span j := by
    have hs := SourceRouting.side_pos S (SelectedInput.input p S hm).precision
    change 0 < 2^54*129*PhysicalParameters.routingSide S (SelectedInput.input p S hm).precision
    rw [PhysicalParameters.routingSide_eq]
    positivity
  have hspan : (1 : ℤ) ≤ 2*(L : ℤ)*(d : ℤ)*(I.span j : ℤ) := by
    have hh : 0 < 2*L*d*I.span j := by positivity
    exact_mod_cast (show 1 ≤ 2*L*d*I.span j by omega)
  have hlo : (0 : ℤ) ≤ (L : ℤ)*(d : ℤ)*
      (placementMatrix.mulVec (SourceDecoration.site S (SelectedInput.input p S hm).precision v)) j :=
    mul_nonneg (by positivity) hv.1
  have hhi := mul_le_mul_of_nonneg_left hv.2 (show (0 : ℤ) ≤ (L : ℤ)*(d : ℤ) by positivity)
  change (margin L t : ℤ) ≤ 2*((translationCell L t : ℤ)+(L : ℤ)*(d : ℤ)*
      (placementMatrix.mulVec (SourceDecoration.site S (SelectedInput.input p S hm).precision v)) j) ∧
    2*((translationCell L t : ℤ)+(L : ℤ)*(d : ℤ)*
      (placementMatrix.mulVec (SourceDecoration.site S (SelectedInput.input p S hm).precision v)) j)+
      (margin L t : ℤ) ≤ 2*((2*L*d*I.span j+4+L+L*t+4 : ℕ) : ℤ)
  push_cast at *
  dsimp only [margin] at *
  push_cast at *
  constructor <;> nlinarith only [hshiftZ.1, hshiftZ.2, hlo, hhi, hspan]

theorem sourceCell_injective (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (k : ℕ) : Function.Injective (sourceCell p S hm k) := by
  intro v w h
  apply SourceDecoration.site_injective S (SelectedInput.input p S hm).precision
  funext j
  have hj := congrArg (fun x : Bloch.Alias => x j) h
  simp only [sourceCell, placementCell, placementMatrix, Matrix.mulVec_diagonal] at hj
  have hLd : (stageLength k : ℤ)*(stageSpacing (sourceInput p S hm) MasterConstants.exponent k : ℤ) ≠ 0 := by
    have hL := stageLength_pos k
    have hd : 0 < stageSpacing (sourceInput p S hm) MasterConstants.exponent k :=
      selectedSpacing_pos _ _ _ _ _ _
    positivity
  have hB : placementDiagonal j ≠ 0 := by fin_cases j <;> norm_num [placementDiagonal]
  exact mul_left_cancel₀ hB (mul_left_cancel₀ hLd (add_left_cancel hj))

theorem sourceCenter_margin (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (k : ℕ) (v : SourceDecoration.Vertex S (SelectedInput.input p S hm).precision) (j : Fin 3) :
    let M := margin (stageLength k) (stageBuffer (sourceInput p S hm) MasterConstants.exponent k)
    (M : ℝ) ≤ latticeShift (sourceCell p S hm k v) j ∧
    latticeShift (sourceCell p S hm k v) j+(M : ℝ) ≤ 2*(sourceBox p S hm k j : ℝ) := by
  have hh := sourceCell_margin p S hm k v j
  simp only [latticeShift, PiLp.smul_apply, integerVector_apply, smul_eq_mul]
  exact_mod_cast hh

theorem sourceBox_count (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (k : ℕ) :
    (∏ j : Fin 3, sourceBox p S hm k j) ≤
      boxCount (stageSpan (sourceInput p S hm) MasterConstants.exponent k)
        (stageLength k) (stageBuffer (sourceInput p S hm) MasterConstants.exponent k) := by
  apply le_trans (Finset.prod_le_prod (fun j (_ : j ∈ Finset.univ) =>
    show sourceBox p S hm k j ≤ 1+2*boxSide
      (stageSpan (sourceInput p S hm) MasterConstants.exponent k)
      (stageLength k) (stageBuffer (sourceInput p S hm) MasterConstants.exponent k) j from by
        rw [← sourceBox_side]
        omega))
  exact Nat.le_mul_of_pos_left _ (by decide : 0 < 2)

#print axioms sourcePlacedSite_bound
#print axioms sourceCell_margin
#print axioms sourceCell_injective
#print axioms sourceBox_count

end Maxwell.Continuum.Parameters
