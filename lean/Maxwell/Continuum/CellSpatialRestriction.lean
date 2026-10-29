import Maxwell.Continuum.CellSpatialExtension

/-! Literal restriction to the physical cell and its adjoint relation to
the proved zero extension. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CellGauge

open CellBandFourier MeasureTheory Set Bloch
open scoped ENNReal InnerProduct

theorem cell_mean_coe_measurePreserving :
    MeasurePreserving (Subtype.val : physicalCell → Space) cellMeanMeasure
      ((1 / 8 : ENNReal) • volume.restrict physicalCell) where
  measurable := measurable_subtype_coe
  map_eq := by
    rw [Measure.map_smul _ measurable_subtype_coe.aemeasurable,
      map_comap_subtype_coe physicalCell_measurable]

theorem cell_coe_ae {f g : Space → ℂ} (hfg : f =ᵐ[volume] g) :
    (fun x : physicalCell => f x.val) =ᵐ[cellMeanMeasure] fun x => g x.val :=
  cell_mean_coe_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (Measure.ae_smul_measure (ae_restrict_of_ae hfg) (1/8 : ENNReal))

theorem restrictScalar_memLp (f : ScalarL2) :
    MemLp (fun x : physicalCell => f x.val) 2 cellMeanMeasure :=
  (((Lp.memLp f).restrict physicalCell).smul_measure
    (by norm_num : (1/8 : ENNReal) ≠ ∞)).comp_measurePreserving cell_mean_coe_measurePreserving

def restrictScalar (f : ScalarL2) : PhysicalScalarCellL2 := (restrictScalar_memLp f).toLp _

theorem restrictScalar_ae (f : ScalarL2) :
    restrictScalar f =ᵐ[cellMeanMeasure] fun x => f x.val := MemLp.coeFn_toLp _

theorem restrictScalar_norm_le (f : ScalarL2) : ‖restrictScalar f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (restrictScalar_ae f)]
  apply ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
  change eLpNorm ((f : Space → ℂ) ∘ Subtype.val) 2 cellMeanMeasure ≤ _
  rw [eLpNorm_comp_measurePreserving
    ((Lp.aestronglyMeasurable f).restrict.smul_measure _) cell_mean_coe_measurePreserving]
  apply eLpNorm_mono_measure
  apply le_trans _ (Measure.restrict_le_self (μ := (volume : Measure Space))
    (s := physicalCell))
  apply Measure.le_iff.mpr
  intro s _
  change (1/8 : ENNReal) * volume.restrict physicalCell s ≤ volume.restrict physicalCell s
  calc
    _ ≤ (1 : ENNReal) * volume.restrict physicalCell s := by gcongr; norm_num
    _ = _ := one_mul _

def restrictScalarLinear : ScalarL2 →ₗ[ℂ] PhysicalScalarCellL2 where
  toFun := restrictScalar
  map_add' f g := by
    apply Lp.ext
    filter_upwards [restrictScalar_ae (f+g), restrictScalar_ae f, restrictScalar_ae g,
      cell_coe_ae (Lp.coeFn_add f g), Lp.coeFn_add (restrictScalar f) (restrictScalar g)]
      with x hfg hf hg ha hb
    rw [hfg, hb, ha]
    simp only [Pi.add_apply, hf, hg]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [restrictScalar_ae (c • f), restrictScalar_ae f,
      cell_coe_ae (Lp.coeFn_smul c f), Lp.coeFn_smul c (restrictScalar f)] with x hcf hf ha hb
    change restrictScalar (c • f) x = (c • restrictScalar f) x
    rw [hcf, hb, ha]
    simp only [Pi.smul_apply, hf]

def restrictScalarCLM : ScalarL2 →L[ℂ] PhysicalScalarCellL2 :=
  restrictScalarLinear.mkContinuous 1 (fun f => by
    change ‖restrictScalar f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using restrictScalar_norm_le f)

theorem restrict_extend (f : PhysicalScalarCellL2) : restrictScalar (extendScalar f) = f := by
  apply Lp.ext
  filter_upwards [restrictScalar_ae (extendScalar f), cell_coe_ae (extendScalar_ae f)] with x hr he
  rw [hr, he, extendFunction_coe]

theorem extend_restrict (f : ScalarL2) :
    extendScalar (restrictScalar f) =ᵐ[volume] physicalCell.indicator (fun x => f x) := by
  filter_upwards [extendScalar_ae (restrictScalar f), extendFunction_ae_congr (restrictScalar_ae f)]
    with x he hr
  rw [he, hr]
  by_cases hx : x ∈ physicalCell
  · rw [indicator_of_mem hx]
    exact extendFunction_coe (fun y : physicalCell => f y.val) ⟨x,hx⟩
  · rw [indicator_of_notMem hx, extendFunction_zero _ hx]

theorem extendScalar_pairing (f : PhysicalScalarCellL2) (g : ScalarL2) :
    inner ℂ (extendScalar f) g = (8 : ℂ) * inner ℂ f (restrictScalar g) := by
  rw [L2.inner_def, L2.inner_def]
  have he : (fun x => inner ℂ (extendScalar f x) (g x)) =ᵐ[volume]
      extendFunction (fun y : physicalCell => inner ℂ (f y) (g y.val)) := by
    filter_upwards [extendScalar_ae f] with x hx
    rw [hx]
    by_cases hc : x ∈ physicalCell
    · change inner ℂ (extendFunction f (⟨x,hc⟩ : physicalCell).val) (g x) =
        extendFunction (fun y : physicalCell => inner ℂ (f y) (g y.val)) (⟨x,hc⟩ : physicalCell).val
      rw [extendFunction_coe, extendFunction_coe]
    · rw [extendFunction_zero f hc, inner_zero_left, extendFunction_zero _ hc]
  rw [integral_congr_ae he, extendFunction_integral]
  change (8 : ℂ) * (∫ y : physicalCell, inner ℂ (f y) (g y.val) ∂cellMeanMeasure) = _
  congr 1
  apply integral_congr_ae
  filter_upwards [restrictScalar_ae g] with y hy
  rw [hy]

def restrictField : FieldL2 →L[ℂ] PhysicalCellL2 :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => PhysicalScalarCellL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => restrictScalarCLM.comp (PiLp.proj 2 _ j)))

theorem restrictField_norm_le (f : FieldL2) : ‖restrictField f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _)
    (restrictScalar_norm_le (f j)) 2

def restrictCell : FieldL2 →L[ℂ] CellFieldL2 :=
  spatialUnitary.toContinuousLinearEquiv.toContinuousLinearMap.comp restrictField

theorem restrictCell_norm_le (f : FieldL2) : ‖restrictCell f‖ ≤ ‖f‖ := by
  change ‖spatialUnitary (restrictField f)‖ ≤ _
  rw [spatialUnitary.norm_map]
  exact restrictField_norm_le f

theorem embedCell_restrictCell (f : FieldL2) (j : Fin 3) :
    embedCell (restrictCell f) j =ᵐ[volume] physicalCell.indicator (fun x => f j x) := by
  change extendField (spatialUnitary.symm (spatialUnitary (restrictField f))) j =ᵐ[volume] _
  rw [spatialUnitary.symm_apply_apply]
  exact extend_restrict (f j)

theorem embedCell_pairing (f : CellFieldL2) (g : FieldL2) :
    inner ℂ (embedCell f) g = (8 : ℂ) * inner ℂ f (restrictCell g) := by
  change inner ℂ (extendField (spatialUnitary.symm f)) g =
    (8 : ℂ) * inner ℂ f (spatialUnitary (restrictField g))
  have he := spatialUnitary.inner_map_map (spatialUnitary.symm f) (restrictField g)
  rw [spatialUnitary.apply_symm_apply] at he
  rw [he, PiLp.inner_apply, PiLp.inner_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => extendScalar_pairing ((spatialUnitary.symm f) j) (g j)

theorem restrictCell_eq_adjoint : restrictCell = (1/8 : ℂ) • (embedCell†) := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [smul_apply, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    embedCell_pairing]
  ring

#print axioms embedCell_restrictCell
#print axioms restrictCell_eq_adjoint

end Maxwell.Continuum.CellGauge
