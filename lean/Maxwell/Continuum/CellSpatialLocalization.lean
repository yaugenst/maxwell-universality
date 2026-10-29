import Maxwell.Continuum.CellSpatialRestriction
import Maxwell.Continuum.CellSpatialTranslation

/-! Literal spatial cell projections, with exact adjoint normalization.
The half-open physical cells have side length two and are translated by
the actual lattice vectors used in the Bloch transform. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open CellBandFourier Bloch MeasureTheory Set
open scoped InnerProduct

def spatialBox (a : Bloch.Alias) : Set Space :=
  {x | x - latticeShift a ∈ physicalCell}

theorem spatialBox_measurable (a : Bloch.Alias) : MeasurableSet (spatialBox a) :=
  physicalCell_measurable.preimage (measurable_id.sub_const _)

def restrictLatticeCell (a : Bloch.Alias) : FieldL2 →L[ℂ] CellFieldL2 :=
  restrictCell.comp (translationOperator (latticeShift a))

def cellProjection (a : Bloch.Alias) : FieldL2 →L[ℂ] FieldL2 :=
  (embedLatticeCell a).comp (restrictLatticeCell a)

theorem restrictLatticeCell_norm_le (a : Bloch.Alias) (f : FieldL2) :
    ‖restrictLatticeCell a f‖ ≤ ‖f‖ := by
  change ‖restrictCell (fieldTranslation (latticeShift a) f)‖ ≤ _
  simpa only [(fieldTranslation (latticeShift a)).norm_map] using
    restrictCell_norm_le (fieldTranslation (latticeShift a) f)

theorem embedLatticeCell_norm_le (a : Bloch.Alias) (f : CellFieldL2) :
    ‖embedLatticeCell a f‖ ≤ 3 * ‖f‖ := by
  have hn := embedLatticeCell_norm_sq a f
  nlinarith [norm_nonneg (embedLatticeCell a f), norm_nonneg f, sq_nonneg ‖f‖]

theorem embedLatticeCell_pairing (a : Bloch.Alias) (f : CellFieldL2) (g : FieldL2) :
    inner ℂ (embedLatticeCell a f) g =
      (8 : ℂ) * inner ℂ f (restrictLatticeCell a g) := by
  have hi := (fieldTranslation (latticeShift a)).inner_map_map
    (fieldTranslation (-latticeShift a) (embedCell f)) g
  rw [fieldTranslation_neg_apply] at hi
  change inner ℂ (fieldTranslation (-latticeShift a) (embedCell f)) g = _
  rw [← hi, embedCell_pairing]
  rfl

theorem restrictLatticeCell_eq_adjoint (a : Bloch.Alias) :
    restrictLatticeCell a = (1/8 : ℂ) • ((embedLatticeCell a)†) := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [smul_apply, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    embedLatticeCell_pairing]
  ring

theorem cellProjection_ae (a : Bloch.Alias) (f : FieldL2) (j : Fin 3) :
    cellProjection a f j =ᵐ[volume] (spatialBox a).indicator (fun x => f j x) := by
  have hp := (measurePreserving_add_right volume (-latticeShift a)).quasiMeasurePreserving.ae_eq_comp
    (embedCell_restrictCell (fieldTranslation (latticeShift a) f) j)
  have ht := (measurePreserving_add_right volume (-latticeShift a)).quasiMeasurePreserving.ae_eq_comp
    (fieldTranslation_ae (latticeShift a) f j)
  change fieldTranslation (-latticeShift a)
    (embedCell (restrictCell (fieldTranslation (latticeShift a) f))) j =ᵐ[volume] _
  filter_upwards [fieldTranslation_ae (-latticeShift a)
    (embedCell (restrictCell (fieldTranslation (latticeShift a) f))) j, hp, ht] with x he hp ht
  dsimp only [Function.comp_apply] at hp ht
  rw [he, hp]
  by_cases hx : x ∈ spatialBox a
  · have hx' : x + -latticeShift a ∈ physicalCell := hx
    rw [indicator_of_mem hx', indicator_of_mem hx, ht]
    simp only [neg_add_cancel_right]
  · have hx' : x + -latticeShift a ∉ physicalCell := hx
    rw [indicator_of_notMem hx', indicator_of_notMem hx]

theorem cellProjection_norm_le (a : Bloch.Alias) : ‖cellProjection a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro j _
  apply pow_le_pow_left₀ (norm_nonneg _)
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cellProjection_ae a f j] with x hx
  rw [hx]
  by_cases hs : x ∈ spatialBox a
  · rw [indicator_of_mem hs]
  · rw [indicator_of_notMem hs, norm_zero]
    exact norm_nonneg _

theorem cellProjection_idempotent (a : Bloch.Alias) :
    (cellProjection a).comp (cellProjection a) = cellProjection a := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [cellProjection_ae a (cellProjection a f) j,
    cellProjection_ae a f j] with x hg hf
  change cellProjection a (cellProjection a f) j x = cellProjection a f j x
  rw [hg, hf]
  by_cases hs : x ∈ spatialBox a
  · rw [indicator_of_mem hs, hf, indicator_of_mem hs]
  · simp only [indicator_of_notMem hs]

theorem cellProjection_selfAdjoint (a : Bloch.Alias) : IsSelfAdjoint (cellProjection a) := by
  change (cellProjection a)† = cellProjection a
  unfold cellProjection
  rw [restrictLatticeCell_eq_adjoint, ContinuousLinearMap.comp_smul,
    map_smulₛₗ, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  simp only [starRingEnd_apply, star_div₀, star_one, star_ofNat]

#print axioms cellProjection_ae
#print axioms cellProjection_norm_le
#print axioms cellProjection_selfAdjoint

end Maxwell.Continuum.CellGauge
