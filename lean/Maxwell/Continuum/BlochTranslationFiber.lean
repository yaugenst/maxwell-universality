import Maxwell.Continuum.PeriodicMaterialTranslation
import Maxwell.Continuum.BlochPeriodicGraph

/-! The literal infinite-alias phase induced by physical translation.
Its graph identities hold on the full maximal Maxwell domain. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory FreeFiber

def translationBlock (a : Space) (q : QuasiCell) (n : Alias) : Polarization →L[ℂ] Polarization :=
  phase a (quasiFrequencyJoin (q,n)) • ContinuousLinearMap.id ℂ Polarization

theorem translationBlock_norm_le (a : Space) (q : QuasiCell) (n : Alias) :
    ‖translationBlock a q n‖ ≤ 1 := by
  rw [translationBlock, norm_smul, phase_norm, one_mul]
  exact ContinuousLinearMap.norm_id_le

def fiberTranslation (a : Space) (q : QuasiCell) : FiberSpace →L[ℂ] FiberSpace :=
  boundedBlocks (translationBlock a q) zero_le_one (translationBlock_norm_le a q)

theorem fiberTranslation_apply (a : Space) (q : QuasiCell) (u : FiberSpace) (n : Alias) :
    fiberTranslation a q u n = phase a (quasiFrequencyJoin (q,n)) • u n := rfl

theorem fiberTranslation_norm_le (a : Space) (q : QuasiCell) :
    ‖fiberTranslation a q‖ ≤ 1 :=
  boundedBlocks_norm_le _ zero_le_one (translationBlock_norm_le a q)

theorem unitary_fieldTranslation_ae (a : Space) (u : FieldL2) :
    unitary (fieldTranslation a u) =ᵐ[quasiMeasure]
      (fun q => fiberTranslation a q (unitary u q)) := by
  filter_upwards [unitary_fieldTranslation_coordinate_ae a u] with q hq
  apply lp.ext
  funext n
  apply PiLp.ext
  intro j
  exact hq n j

theorem fiberTranslation_free_graph (a : Space) (q : QuasiCell) (E : ℂ)
    (u v : FiberSpace) (h : (u,v) ∈ (operator (quasiMomentum q) E).graph) :
    (fiberTranslation a q u, fiberTranslation a q v) ∈
      (operator (quasiMomentum q) E).graph := by
  rw [operator_graph_iff] at h ⊢
  intro n
  rw [fiberTranslation_apply, fiberTranslation_apply, map_smul, h n]

def fiberMaterialCommutator (a : Space) (q : QuasiCell) : FiberSpace →L[ℂ] FiberSpace :=
  (backgroundAmplitude : ℂ) •
    (fiberTranslation a q * potential - potential * fiberTranslation a q)

theorem fiberTranslation_material_graph (a : Space) (q : QuasiCell) (E : ℂ)
    (u v : FiberSpace)
    (h : (u,v) ∈ (materialFiber (quasiMomentum q) E backgroundAmplitude).graph) :
    (fiberTranslation a q u, fiberTranslation a q v + fiberMaterialCommutator a q u) ∈
      (materialFiber (quasiMomentum q) E backgroundAmplitude).graph := by
  rw [materialFiber_graph_iff] at h ⊢
  have hg := fiberTranslation_free_graph a q E u _ h
  have he : fiberTranslation a q v + fiberMaterialCommutator a q u +
      (backgroundAmplitude : ℂ) • potential (fiberTranslation a q u) =
      fiberTranslation a q (v + (backgroundAmplitude : ℂ) • potential u) := by
    change fiberTranslation a q v + (backgroundAmplitude : ℂ) •
      (fiberTranslation a q (potential u) - potential (fiberTranslation a q u)) +
      (backgroundAmplitude : ℂ) • potential (fiberTranslation a q u) = _
    rw [map_add, map_smul, smul_sub]
    abel
  rwa [he]

theorem unitary_dielectric_ae (u : FieldL2) :
    unitary (PeriodicMaterial.dielectric.multiplier u) =ᵐ[quasiMeasure]
      (fun q => (7 : ℂ) • unitary u q +
        (backgroundAmplitude : ℂ) • potential (unitary u q)) := by
  rw [periodicMultiplier_eq, map_add, map_smul, map_smul, unitary_physicalPotential]
  filter_upwards [Lp.coeFn_add ((7 : ℂ) • unitary u)
    ((backgroundAmplitude : ℂ) • potentialL2 (unitary u)),
    Lp.coeFn_smul (7 : ℂ) (unitary u),
    Lp.coeFn_smul (backgroundAmplitude : ℂ) (potentialL2 (unitary u)),
    potentialL2_ae (unitary u)] with q ha h7 hρ hP
  simp only [ha, Pi.add_apply, h7, Pi.smul_apply, hρ, hP]

theorem unitary_translationCommutator_ae (a : Space) (u : FieldL2) :
    unitary (PeriodicMaterial.translationCommutator a u) =ᵐ[quasiMeasure]
      (fun q => fiberMaterialCommutator a q (unitary u q)) := by
  change unitary (fieldTranslation a (PeriodicMaterial.dielectric.multiplier u) -
    PeriodicMaterial.dielectric.multiplier (fieldTranslation a u)) =ᵐ[quasiMeasure] _
  rw [map_sub]
  filter_upwards [Lp.coeFn_sub (unitary (fieldTranslation a
      (PeriodicMaterial.dielectric.multiplier u)))
      (unitary (PeriodicMaterial.dielectric.multiplier (fieldTranslation a u))),
    unitary_fieldTranslation_ae a (PeriodicMaterial.dielectric.multiplier u),
    unitary_dielectric_ae u, unitary_dielectric_ae (fieldTranslation a u),
    unitary_fieldTranslation_ae a u] with q hs ht hε hεt htu
  rw [hs]
  simp only [Pi.sub_apply, ht, hε, hεt, htu]
  change fiberTranslation a q ((7 : ℂ) • unitary u q +
      (backgroundAmplitude : ℂ) • potential (unitary u q)) -
      ((7 : ℂ) • fiberTranslation a q (unitary u q) +
        (backgroundAmplitude : ℂ) • potential (fiberTranslation a q (unitary u q))) =
    (backgroundAmplitude : ℂ) • (fiberTranslation a q (potential (unitary u q)) -
      potential (fiberTranslation a q (unitary u q)))
  rw [map_add, map_smul, map_smul, smul_sub]
  abel

end Maxwell.Continuum.Bloch
