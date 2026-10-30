import Maxwell.Continuum.FiniteAuxiliaryCommonShift
import Maxwell.Continuum.ParameterGeometry
import Maxwell.Continuum.BoxCellGeometry
import Maxwell.Continuum.CellSpatialCover

/-! The actual rational/integer parameter search supplies a buffered
layout with disjoint wells. Its common translation preserves the
assembled continuum response exactly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass PeriodicBand CellGauge Bloch Parameters Maxwell.Composition

theorem shifted_centers_disjoint {ι : Type*} {L d : ℕ} (hL : 0 < (L : ℝ)) (hd : 1 ≤ d)
    (position : ι → Alias) (hinj : Function.Injective position) (a : Space) :
    Pairwise fun i j => Disjoint (Metric.ball (centers L d position i+a) (L : ℝ))
      (Metric.ball (centers L d position j+a) (L : ℝ)) := by
  intro i j hij
  apply Metric.ball_disjoint_ball
  rw [dist_eq_norm, add_sub_add_right_eq_sub, centers_sub, ← two_mul]
  exact placed_integer_norm_lower hL hd (sub_ne_zero.mpr (hinj.ne hij))

def sourceCommonShift (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (k : ℕ) : Alias := fun _ =>
  (translationCell (stageLength k) (stageBuffer (sourceInput p S hm) MasterConstants.exponent k) : ℤ)

theorem source_centers_shift (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (k : ℕ) :
    (fun v => latticeShift (sourceCell p S hm k v)) =
      fun v => centers (stageLength k) (stageSpacing (sourceInput p S hm) MasterConstants.exponent k)
        (SourceDecoration.site S (SelectedInput.input p S hm).precision) v+
        latticeShift (sourceCommonShift p S hm k) := by
  funext v
  change latticeShift (sourceCommonShift p S hm k+
    placementCell (stageLength k) (stageSpacing (sourceInput p S hm) MasterConstants.exponent k)
      (SourceDecoration.site S (SelectedInput.input p S hm).precision v)) = _
  rw [latticeShift_add, add_comm]
  rfl

theorem source_centers_disjoint (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (k : ℕ) :
    Pairwise fun i j => Disjoint
      (Metric.ball (latticeShift (sourceCell p S hm k i)) (stageLength k : ℝ))
      (Metric.ball (latticeShift (sourceCell p S hm k j)) (stageLength k : ℝ)) := by
  have h := shifted_centers_disjoint
    (by exact_mod_cast stageLength_pos k : (0 : ℝ) < stageLength k)
    (show 1 ≤ stageSpacing (sourceInput p S hm) MasterConstants.exponent k from
      selectedSpacing_pos _ _ _ _ _ _)
    (SourceDecoration.site S (SelectedInput.input p S hm).precision)
    (SourceDecoration.site_injective S (SelectedInput.input p S hm).precision)
    (latticeShift (sourceCommonShift p S hm k))
  intro i j hij
  rw [congrFun (source_centers_shift p S hm k) i,
    congrFun (source_centers_shift p S hm k) j]
  exact h hij

theorem source_centers_buffered (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (k : ℕ) (i : SourceDecoration.Vertex S (SelectedInput.input p S hm).precision) (j : Fin 3) :
    (stageLength k : ℝ)*(stageBuffer (sourceInput p S hm) MasterConstants.exponent k : ℝ)+
        (stageLength k : ℝ)+8 ≤ latticeShift (sourceCell p S hm k i) j ∧
      latticeShift (sourceCell p S hm k i) j ≤ BoxCutoff.side (sourceBox p S hm k) j-
        (stageLength k : ℝ)*(stageBuffer (sourceInput p S hm) MasterConstants.exponent k : ℝ)-
        (stageLength k : ℝ)-8 := by
  have he := sourceCenter_margin p S hm k i j
  dsimp only [margin] at he
  push_cast at he
  dsimp only [BoxCutoff.side]
  constructor <;> linarith only [he.1, he.2]

theorem source_auxiliaryMatrix_eq (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (k : ℕ) {z σ : ℝ} (D : Calibration (stageLength k : ℝ)⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (stageLength k : ℝ)⁻¹^4/64)
    (v : SourceDecoration.Vertex S (SelectedInput.input p S hm).precision → ℝ) :
    auxiliaryMatrix D hσ0 hσ (fun i => latticeShift (sourceCell p S hm k i)) v =
      auxiliaryMatrix D hσ0 hσ
        (centers (stageLength k) (stageSpacing (sourceInput p S hm) MasterConstants.exponent k)
          (SourceDecoration.site S (SelectedInput.input p S hm).precision)) v := by
  rw [source_centers_shift]
  exact auxiliaryMatrix_common_lattice_shift D hσ0 hσ _ v (sourceCommonShift p S hm k)

#print axioms source_centers_disjoint
#print axioms source_centers_buffered
#print axioms source_auxiliaryMatrix_eq

end Maxwell.Continuum.FiniteAuxiliary
