import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact normalized-Haar to physical-momentum conversion. The local ball
and its complementary fundamental-cell region share the same concrete
Lebesgue measure, including the factor `(2π)⁻³`. -/
namespace Maxwell.Defect.TorusChart
open MeasureTheory Set

abbrev Momentum := EuclideanSpace ℝ (Fin 3)
abbrev Torus := UnitAddTorus (Fin 3)

noncomputable def haar : Measure Torus :=
  Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle)

noncomputable def unitCell : Set Momentum :=
  {q | ∀ i, -(1 / 2 : ℝ) < q i ∧ q i ≤ 1 / 2}

noncomputable def physicalCell : Set Momentum :=
  {q | ∀ i, -Real.pi < q i ∧ q i ≤ Real.pi}

noncomputable def quotient (q : Momentum) : Torus := fun i => (q i : UnitAddCircle)

noncomputable def momentumTorus (q : Momentum) : Torus :=
  quotient ((2 * Real.pi)⁻¹ • q)

theorem haar_eq_volume : haar = volume := by
  have hc : (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm
  simp only [haar, hc]
  rfl

instance : Measure.IsAddLeftInvariant haar := by
  rw [haar_eq_volume]
  infer_instance

theorem measurableSet_unitCell : MeasurableSet unitCell := by
  have h := MeasurableSet.iInter fun i : Fin 3 =>
    ((measurableSet_Ioc : MeasurableSet (Ioc (-(1 / 2 : ℝ)) (1 / 2))).preimage
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).measurable)
  convert h using 1
  ext q
  simp only [unitCell, mem_ofPred_eq, mem_iInter, mem_preimage, mem_Ioc]

theorem measurableSet_physicalCell : MeasurableSet physicalCell := by
  have h := MeasurableSet.iInter fun i : Fin 3 =>
    ((measurableSet_Ioc : MeasurableSet (Ioc (-Real.pi) Real.pi)).preimage
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).measurable)
  convert h using 1
  ext q
  simp only [physicalCell, mem_ofPred_eq, mem_iInter, mem_preimage, mem_Ioc]

theorem quotient_measurePreserving :
    MeasurePreserving quotient (volume.restrict unitCell) haar := by
  let cube : Set (Fin 3 → ℝ) := Set.univ.pi fun _ => Ioc (-(1 / 2 : ℝ)) (1 / 2)
  have hcube : MeasurableSet cube := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hraw : MeasurePreserving (fun q : Fin 3 → ℝ => fun i => (q i : UnitAddCircle))
      (volume.restrict cube) (volume : Measure Torus) := by
    have hp := measurePreserving_pi
      (fun _ : Fin 3 => volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2)))
      (fun _ : Fin 3 => (volume : Measure UnitAddCircle))
      (f := fun _ q => (q : UnitAddCircle))
      (fun _ => by convert UnitAddCircle.measurePreserving_mk (-(1 / 2 : ℝ)) using 1; norm_num)
    rw [← Measure.restrict_pi_pi] at hp
    exact hp
  have hcoord := (PiLp.volume_preserving_ofLp (Fin 3)).restrict_preimage hcube
  have hcell : WithLp.ofLp ⁻¹' cube = unitCell := by
    ext q
    simp [cube, unitCell]
  rw [hcell] at hcoord
  rw [haar_eq_volume]
  exact hraw.comp hcoord

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual quotient map pushes unit-cell Lebesgue measure to normalized
Haar measure. No Fourier or change-of-variables oracle is assumed. -/
theorem integral_unitCell (f : Torus → F) (hf : AEStronglyMeasurable f haar) :
    (∫ q in unitCell, f (quotient q)) = ∫ t, f t ∂haar := by
  have hp := quotient_measurePreserving
  have hh := integral_map hp.aemeasurable (hp.map_eq.symm ▸ hf)
  rw [hp.map_eq] at hh
  exact hh.symm

theorem scale_cell_iff (q : Momentum) :
    (2 * Real.pi) • q ∈ physicalCell ↔ q ∈ unitCell := by
  have hπ := Real.pi_pos
  simp only [physicalCell, unitCell, mem_ofPred_eq, PiLp.smul_apply, smul_eq_mul]
  constructor <;> intro h i <;> obtain ⟨hl, hu⟩ := h i
  · constructor <;> nlinarith
  · constructor <;> nlinarith

theorem momentum_scale (q : Momentum) : momentumTorus ((2 * Real.pi) • q) = quotient q := by
  unfold momentumTorus
  rw [smul_smul, inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]

/-- Exact physical momentum normalization on the centered Brillouin cell. -/
theorem integral_physicalCell (f : Torus → F) (hf : AEStronglyMeasurable f haar) :
    (∫ t, f t ∂haar) = (1 / (2 * Real.pi) ^ 3 : ℝ) •
      ∫ q in physicalCell, f (momentumTorus q) := by
  rw [← integral_unitCell f hf, ← integral_indicator measurableSet_unitCell,
    ← integral_indicator measurableSet_physicalCell]
  have hid : unitCell.indicator (fun q => f (quotient q)) =
      fun q => physicalCell.indicator (fun p => f (momentumTorus p)) ((2 * Real.pi) • q) := by
    funext q
    by_cases hq : q ∈ unitCell
    · simp [hq, (scale_cell_iff q).mpr hq, momentum_scale]
    · have hq' : (2 * Real.pi) • q ∉ physicalCell := fun h => hq ((scale_cell_iff q).mp h)
      simp [hq, hq']
  rw [hid, Measure.integral_comp_smul]
  norm_num [abs_of_pos Real.pi_pos]

omit [NormedSpace ℝ F] in
/-- Integrability transfers through the same concrete quotient and
physical-coordinate scaling used by the exact integral identity. -/
theorem integrable_physicalCell (f : Torus → F) (hf : Integrable f haar) :
    IntegrableOn (fun q => f (momentumTorus q)) physicalCell := by
  have hu : IntegrableOn (fun q => f (quotient q)) unitCell :=
    (quotient_measurePreserving.integrable_comp hf.aestronglyMeasurable).mpr hf
  apply (integrable_indicator_iff measurableSet_physicalCell).mp
  apply (integrable_comp_smul_iff volume _
    (by positivity : 2 * Real.pi ≠ 0)).mp
  have hid : (fun q => physicalCell.indicator (fun p => f (momentumTorus p))
      ((2 * Real.pi) • q)) = unitCell.indicator (fun q => f (quotient q)) := by
    funext q
    by_cases hq : q ∈ unitCell
    · simp [hq, (scale_cell_iff q).mpr hq, momentum_scale]
    · have hq' : (2 * Real.pi) • q ∉ physicalCell := fun h => hq ((scale_cell_iff q).mp h)
      simp [hq, hq']
  rw [hid]
  exact (integrable_indicator_iff measurableSet_unitCell).mpr hu

/-- Any edge location can be used as the center; normalized Haar measure
is translation invariant and the physical Jacobian stays `(2π)⁻³`. -/
theorem integral_centered_physicalCell (f : Torus → F)
    (hf : AEStronglyMeasurable f haar) (center : Torus) :
    (∫ t, f t ∂haar) = (1 / (2 * Real.pi) ^ 3 : ℝ) •
      ∫ q in physicalCell, f (center + momentumTorus q) := by
  have ht := hf.comp_measurePreserving (measurePreserving_add_left haar center)
  have hh := integral_physicalCell (fun t => f (center + t)) ht
  rw [integral_add_left_eq_self] at hh
  exact hh

theorem ball_subset_physicalCell {r : ℝ} (hr : r ≤ Real.pi) :
    Metric.ball (0 : Momentum) r ⊆ physicalCell := by
  intro q hq
  have hqr : ‖q‖ < r := by simpa using hq
  intro i
  have hi : |q i| < Real.pi :=
    (PiLp.norm_apply_le q i).trans_lt (hqr.trans_le hr)
  exact ⟨(abs_lt.mp hi).1, (abs_lt.mp hi).2.le⟩

/-- The concrete Bloch integral splits into its physical local ball and
an explicitly defined far region, with the exact manuscript normalization. -/
theorem integral_local_far (f : Torus → F) (hf : Integrable f haar)
    (center : Torus) {r : ℝ} (hr : r ≤ Real.pi) :
    (∫ t, f t ∂haar) = (1 / (2 * Real.pi) ^ 3 : ℝ) •
      ((∫ q in Metric.ball (0 : Momentum) r, f (center + momentumTorus q)) +
        ∫ q in physicalCell \ Metric.ball (0 : Momentum) r, f (center + momentumTorus q)) := by
  have ht : Integrable (fun t => f (center + t)) haar :=
    ((measurePreserving_add_left haar center).integrable_comp hf.aestronglyMeasurable).mpr hf
  have hp := integrable_physicalCell (fun t => f (center + t)) ht
  rw [integral_centered_physicalCell f hf.aestronglyMeasurable center,
    setIntegral_sdiff measurableSet_ball hp (ball_subset_physicalCell hr)]
  congr 1
  abel

end Maxwell.Defect.TorusChart
