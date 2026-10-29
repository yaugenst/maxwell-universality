import Maxwell.Continuum.BlochCellChange

/-! The regrouped transform on the physical half-open Brillouin cube.
Its measure is literally (2π)^(-3) times dq, times alias counting measure. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory Set
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

def corner : Space := WithLp.toLp 2 (fun _ => Real.pi / 2)

def quasiAmbient : Space ≃ᵐ Space where
  toFun x := Real.pi • x - corner
  invFun q := Real.pi⁻¹ • (q + corner)
  left_inv x := by
    change Real.pi⁻¹ • ((Real.pi • x - corner) + corner) = x
    rw [sub_add_cancel, smul_smul, inv_mul_cancel₀ Real.pi_ne_zero, one_smul]
  right_inv q := by
    change Real.pi • (Real.pi⁻¹ • (q + corner)) - corner = q
    rw [smul_smul, mul_inv_cancel₀ Real.pi_ne_zero, one_smul, add_sub_cancel_right]
  measurable_toFun := (measurable_const_smul Real.pi).sub measurable_const
  measurable_invFun := (measurable_id.add measurable_const).const_smul Real.pi⁻¹

def quasiCell : Set Space := {q | ∀ i, -Real.pi / 2 ≤ q i ∧ q i < Real.pi / 2}
abbrev QuasiCell := quasiCell

theorem quasiCell_measurable : MeasurableSet quasiCell := by
  change MeasurableSet {q : Space | ∀ i, q i ∈ Ico (-Real.pi / 2) (Real.pi / 2)}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun i => measurableSet_Ico.preimage
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin 3 → ℝ)))

theorem unitCell_iff_quasiCell (x : Space) : x ∈ unitCell ↔ quasiAmbient x ∈ quasiCell := by
  change (∀ i, 0 ≤ x i ∧ x i < 1) ↔
    (∀ i, -Real.pi / 2 ≤ Real.pi * x i - Real.pi / 2 ∧
      Real.pi * x i - Real.pi / 2 < Real.pi / 2)
  constructor <;> intro h i <;> have hi := h i
  · constructor <;> nlinarith [Real.pi_pos]
  · constructor <;> nlinarith [Real.pi_pos]

theorem quasiAmbient_measurePreserving :
    MeasurePreserving quasiAmbient volume
      (ENNReal.ofReal (Real.pi ^ 3)⁻¹ • (volume : Measure Space)) where
  measurable := quasiAmbient.measurable
  map_eq := by
    have hsub : Measurable (fun q : Space => q - corner) := measurable_id.sub_const corner
    change Measure.map ((fun q : Space => q - corner) ∘ (fun x : Space => Real.pi • x))
      volume = _
    rw [← Measure.map_map hsub (measurable_const_smul Real.pi),
      Measure.map_addHaar_smul volume Real.pi_ne_zero,
      Measure.map_smul _ hsub.aemeasurable]
    have ht : (volume : Measure Space).map (fun q => q - corner) = volume := by
      simpa only [sub_eq_add_neg] using (measurePreserving_add_right volume (-corner)).map_eq
    rw [ht]
    simp only [show Module.finrank ℝ Space = 3 from finrank_euclideanSpace_fin,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg Real.pi_pos.le 3))]

def quasiCellEquiv : Cell ≃ᵐ QuasiCell :=
  cellEquiv quasiAmbient unitCell quasiCell unitCell_iff_quasiCell

/-- The physical q measure, expressed against the actual restricted
Euclidean Lebesgue measure on the half-open cube. -/
def quasiMeasure : Measure QuasiCell :=
  ENNReal.ofReal ((2 * Real.pi) ^ 3)⁻¹ • (volume.comap (Subtype.val : QuasiCell → Space))

instance quasiVolume_sigmaFinite :
    SigmaFinite (volume.comap (Subtype.val : QuasiCell → Space)) := by
  apply SigmaFinite.of_map _ (f := (Subtype.val : QuasiCell → Space))
    measurable_subtype_coe.aemeasurable
  rw [map_comap_subtype_coe quasiCell_measurable]
  infer_instance

instance quasiMeasure_sigmaFinite : SigmaFinite quasiMeasure := by
  change SigmaFinite ((Real.toNNReal (((2 * Real.pi) ^ 3)⁻¹)) •
    (volume.comap (Subtype.val : QuasiCell → Space)))
  infer_instance

theorem jacobian_coefficient :
    (1 / 8 : ENNReal) * ENNReal.ofReal (Real.pi ^ 3)⁻¹ =
      ENNReal.ofReal ((2 * Real.pi) ^ 3)⁻¹ := by
  have h : (1 / 8 : ENNReal) = ENNReal.ofReal (1 / 8 : ℝ) := by
    rw [one_div, one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8),
      ENNReal.ofReal_ofNat]
  rw [h, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
  congr 1
  field_simp
  ring

theorem quasiCellEquiv_measurePreserving :
    MeasurePreserving quasiCellEquiv normalizedCellMeasure quasiMeasure := by
  have h := (cellEquiv_measurePreserving quasiAmbient quasiAmbient_measurePreserving
    unitCell quasiCell unitCell_measurable quasiCell_measurable
    unitCell_iff_quasiCell).smul_measure (1 / 8 : ENNReal)
  simpa only [quasiCellEquiv, normalizedCellMeasure, cellMeasure, quasiMeasure,
    Measure.comap_smul, smul_smul, jacobian_coefficient] using h

def quasiFrequencyJoin : QuasiCell × Alias ≃ᵐ Space :=
  (quasiCellEquiv.symm.prodCongr (MeasurableEquiv.refl Alias)).trans frequencyJoin

theorem quasiFrequencyJoin_measurePreserving :
    MeasurePreserving quasiFrequencyJoin (quasiMeasure.prod Measure.count) volume := by
  have h := frequencyJoin_measurePreserving.comp
    (quasiCellEquiv_measurePreserving.symm.prod (MeasurePreserving.id (Measure.count : Measure Alias)))
  exact h

@[simp] theorem quasiFrequencyJoin_apply (q : QuasiCell) (n : Alias) (i : Fin 3) :
    quasiFrequencyJoin (q, n) i =
      ((q : Space) i + Real.pi / 2 + Real.pi * (n i : ℝ)) / (2 * Real.pi) := by
  change frequencyJoin (quasiCellEquiv.symm q, n) i = _
  rw [frequencyJoin_apply]
  change (Real.pi⁻¹ * ((q : Space) i + Real.pi / 2) + (n i : ℝ)) / 2 = _
  field_simp

abbrev QuasiAliasL2 := Lp ℂ 2 (quasiMeasure.prod (Measure.count : Measure Alias))
abbrev QuasiAliasFieldL2 := PiLp 2 (fun _ : Fin 3 => QuasiAliasL2)

def quasiRegroup : ScalarL2 ≃ₗᵢ[ℂ] QuasiAliasL2 :=
  measureEquivL2 quasiFrequencyJoin quasiFrequencyJoin_measurePreserving

/-- The actual Fourier/Bloch alias regrouping on physical q coordinates. -/
def quasiTransform : FieldL2 ≃ₗᵢ[ℂ] QuasiAliasFieldL2 :=
  fieldFourier.trans
    (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 3 => quasiRegroup))

theorem quasiTransform_norm (u : FieldL2) : ‖quasiTransform u‖ = ‖u‖ :=
  quasiTransform.norm_map u

theorem quasiTransform_inner (u v : FieldL2) :
    inner ℂ (quasiTransform u) (quasiTransform v) = inner ℂ u v :=
  quasiTransform.inner_map_map u v

theorem quasiTransform_ae (u : FieldL2) (i : Fin 3) :
    quasiTransform u i =ᵐ[quasiMeasure.prod Measure.count]
      (fun qn => fieldFourier u i (quasiFrequencyJoin qn)) :=
  measureEquivL2_ae quasiFrequencyJoin quasiFrequencyJoin_measurePreserving (fieldFourier u i)

end Maxwell.Continuum.Bloch
