import Maxwell.Continuum.CellSpatialEquiv
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Literal zero extension from a physical cell to Euclidean space.
Its factor of eight is proved from the cell measure, not stipulated. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CellGauge

open CellBandFourier MeasureTheory Set Bloch
open scoped ENNReal

instance cellMean_probability : IsProbabilityMeasure cellMeanMeasure := by
  rw [← spatialEquiv_measurePreserving.map_eq]
  infer_instance

theorem cell_volume_from_mean :
    volume.comap (Subtype.val : physicalCell → Space) = (8 : ENNReal) • cellMeanMeasure := by
  change _ = (8 : ENNReal) • ((1 / 8 : ENNReal) • _)
  rw [smul_smul, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_smul]

theorem cell_coe_measurePreserving :
    MeasurePreserving (Subtype.val : physicalCell → Space) ((8 : ENNReal) • cellMeanMeasure)
      (volume.restrict physicalCell) where
  measurable := measurable_subtype_coe
  map_eq := by
    rw [← cell_volume_from_mean, map_comap_subtype_coe physicalCell_measurable]

def extendFunction {F : Type*} [Zero F] (f : physicalCell → F) : Space → F :=
  Function.extend (Subtype.val : physicalCell → Space) f (fun _ => 0)

theorem extendFunction_coe {F : Type*} [Zero F] (f : physicalCell → F) (x : physicalCell) :
    extendFunction f x.val = f x := Function.Injective.extend_apply Subtype.val_injective _ _ _

theorem extendFunction_zero {F : Type*} [Zero F] (f : physicalCell → F)
    {x : Space} (hx : x ∉ physicalCell) : extendFunction f x = 0 := by
  apply Function.extend_apply'
  rintro ⟨y, hy⟩
  exact hx (hy ▸ y.property)

theorem extendFunction_indicator {F : Type*} [Zero F] (f : physicalCell → F) :
    physicalCell.indicator (extendFunction f) = extendFunction f := by
  funext x
  by_cases hx : x ∈ physicalCell
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, extendFunction_zero f hx]

theorem extendFunction_eLpNorm (f : physicalCell → ℂ) (p : ENNReal) :
    eLpNorm (extendFunction f) p volume = eLpNorm f p ((8 : ENNReal) • cellMeanMeasure) := by
  rw [← extendFunction_indicator f, eLpNorm_indicator_eq_eLpNorm_restrict physicalCell_measurable,
    ← cell_coe_measurePreserving.map_eq]
  rw [(MeasurableEmbedding.subtype_coe physicalCell_measurable).eLpNorm_map_measure]
  congr 1
  funext x
  exact extendFunction_coe f x

theorem extendFunction_ae_congr {f g : physicalCell → ℂ} (hfg : f =ᵐ[cellMeanMeasure] g) :
    extendFunction f =ᵐ[(volume : Measure Space)] extendFunction g := by
  have hr : extendFunction f =ᵐ[volume.restrict physicalCell] extendFunction g := by
    rw [← cell_coe_measurePreserving.map_eq]
    apply (MeasurableEmbedding.subtype_coe physicalCell_measurable).ae_map_iff.mpr
    filter_upwards [Measure.ae_smul_measure hfg (8 : ENNReal)] with x hx
    simpa only [extendFunction_coe] using hx
  filter_upwards [(ae_restrict_iff' physicalCell_measurable).mp hr] with x hx
  by_cases hc : x ∈ physicalCell
  · exact hx hc
  · rw [extendFunction_zero f hc, extendFunction_zero g hc]

def extendScalar (f : PhysicalScalarCellL2) : ScalarL2 :=
  (show MemLp (extendFunction f) 2 volume from by
    change eLpNorm (extendFunction f) 2 volume < ∞
    rw [extendFunction_eLpNorm]
    exact (Lp.memLp f).smul_measure (by norm_num : (8 : ENNReal) ≠ ∞)).toLp _

theorem extendScalar_ae (f : PhysicalScalarCellL2) :
    extendScalar f =ᵐ[(volume : Measure Space)] extendFunction f := MemLp.coeFn_toLp _

theorem extendFunction_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : physicalCell → F) :
    (∫ x, extendFunction f x) = (8 : ℝ) • ∫ x, f x ∂cellMeanMeasure := by
  rw [← extendFunction_indicator f, integral_indicator physicalCell_measurable]
  rw [← cell_coe_measurePreserving.integral_comp
    (MeasurableEmbedding.subtype_coe physicalCell_measurable) (extendFunction f)]
  simp only [extendFunction_coe, integral_smul_measure, ENNReal.toReal_ofNat]

theorem extendScalar_norm_sq (f : PhysicalScalarCellL2) : ‖extendScalar f‖^2 = 8 * ‖f‖^2 := by
  rw [complexL2_norm_sq, complexL2_norm_sq]
  have he : (fun x : Space => ‖extendScalar f x‖^2) =ᵐ[volume]
      extendFunction (fun x : physicalCell => ‖f x‖^2) := by
    filter_upwards [extendScalar_ae f] with x hx
    rw [hx]
    by_cases hc : x ∈ physicalCell
    · change ‖extendFunction f (⟨x,hc⟩ : physicalCell).val‖^2 =
        extendFunction (fun y : physicalCell => ‖f y‖^2) (⟨x,hc⟩ : physicalCell).val
      rw [extendFunction_coe, extendFunction_coe]
    · rw [extendFunction_zero f hc, extendFunction_zero _ hc, norm_zero, zero_pow (by omega)]
  rw [integral_congr_ae he, extendFunction_integral, smul_eq_mul]

theorem extendScalar_norm_le (f : PhysicalScalarCellL2) : ‖extendScalar f‖ ≤ 3 * ‖f‖ := by
  have he := extendScalar_norm_sq f
  nlinarith [norm_nonneg f, norm_nonneg (extendScalar f), sq_nonneg ‖f‖]

def extendScalarLinear : PhysicalScalarCellL2 →ₗ[ℂ] ScalarL2 where
  toFun := extendScalar
  map_add' f g := by
    apply Lp.ext
    filter_upwards [extendScalar_ae (f+g), extendScalar_ae f, extendScalar_ae g,
      extendFunction_ae_congr (Lp.coeFn_add f g),
      Lp.coeFn_add (extendScalar f) (extendScalar g)] with x hfg hf hg ha hb
    rw [hfg, hb, ha]
    change extendFunction (fun y => f y + g y) x = extendScalar f x + extendScalar g x
    rw [hf, hg]
    by_cases hx : x ∈ physicalCell
    · change extendFunction (fun y => f y + g y) (⟨x,hx⟩ : physicalCell).val = _
      rw [extendFunction_coe, extendFunction_coe f ⟨x,hx⟩, extendFunction_coe g ⟨x,hx⟩]
    · rw [extendFunction_zero _ hx, extendFunction_zero _ hx, extendFunction_zero _ hx, zero_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [extendScalar_ae (c • f), extendScalar_ae f,
      extendFunction_ae_congr (Lp.coeFn_smul c f), Lp.coeFn_smul c (extendScalar f)]
      with x hcf hf ha hb
    change extendScalar (c • f) x = (c • extendScalar f) x
    rw [hcf, hb, ha]
    change extendFunction (fun y => c * f y) x = c * extendScalar f x
    rw [hf]
    by_cases hx : x ∈ physicalCell
    · change extendFunction (fun y => c * f y) (⟨x,hx⟩ : physicalCell).val = _
      rw [extendFunction_coe, extendFunction_coe f ⟨x,hx⟩]
    · rw [extendFunction_zero _ hx, extendFunction_zero _ hx, mul_zero]

def extendScalarCLM : PhysicalScalarCellL2 →L[ℂ] ScalarL2 :=
  extendScalarLinear.mkContinuous 3 extendScalar_norm_le

def extendField : PhysicalCellL2 →L[ℂ] FieldL2 :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => extendScalarCLM.comp (PiLp.proj 2 _ j)))

theorem extendField_ae (f : PhysicalCellL2) (j : Fin 3) :
    extendField f j =ᵐ[(volume : Measure Space)] extendFunction (f j) := extendScalar_ae (f j)

theorem extendField_norm_sq (f : PhysicalCellL2) : ‖extendField f‖^2 = 8 * ‖f‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => extendScalar_norm_sq (f j)

theorem extendField_norm_le (f : PhysicalCellL2) : ‖extendField f‖ ≤ 3 * ‖f‖ := by
  have he := extendField_norm_sq f
  nlinarith [norm_nonneg f, norm_nonneg (extendField f), sq_nonneg ‖f‖]

def embedCell : CellFieldL2 →L[ℂ] FieldL2 :=
  extendField.comp spatialUnitary.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem embedCell_norm_sq (f : CellFieldL2) : ‖embedCell f‖^2 = 8 * ‖f‖^2 := by
  rw [embedCell, ContinuousLinearMap.comp_apply, extendField_norm_sq]
  change 8 * ‖spatialUnitary.symm f‖^2 = 8 * ‖f‖^2
  rw [spatialUnitary.symm.norm_map]

#print axioms extendScalar_norm_sq
#print axioms extendField_ae
#print axioms embedCell_norm_sq

end Maxwell.Continuum.CellGauge
