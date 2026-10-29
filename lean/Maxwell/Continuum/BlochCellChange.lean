import Maxwell.Continuum.BlochNormalization

/-! Restrict a proved measure equivalence to corresponding measurable cells.
This supplies the change from the unit-cell coordinate to physical q. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory Set

set_option backward.isDefEq.respectTransparency false

section General

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def cellEquiv (e : X ≃ᵐ Y) (s : Set X) (t : Set Y)
    (h : ∀ x, x ∈ s ↔ e x ∈ t) : s ≃ᵐ t where
  toFun x := ⟨e x, (h x).mp x.property⟩
  invFun y := ⟨e.symm y, (h (e.symm y)).mpr (by simpa only [e.apply_symm_apply] using y.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  measurable_toFun := (e.measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := (e.symm.measurable.comp measurable_subtype_coe).subtype_mk

theorem cellEquiv_measurePreserving (e : X ≃ᵐ Y) {μ : Measure X} {ν : Measure Y}
    (he : MeasurePreserving e μ ν) (s : Set X) (t : Set Y)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (h : ∀ x, x ∈ s ↔ e x ∈ t) :
    MeasurePreserving (cellEquiv e s t h) (μ.comap Subtype.val) (ν.comap Subtype.val) where
  measurable := (cellEquiv e s t h).measurable
  map_eq := by
    apply (MeasurableEmbedding.subtype_coe ht).map_injective
    rw [Measure.map_map measurable_subtype_coe (cellEquiv e s t h).measurable]
    change Measure.map (e ∘ (Subtype.val : s → X)) (μ.comap Subtype.val) = _
    rw [← Measure.map_map e.measurable measurable_subtype_coe,
      map_comap_subtype_coe hs, map_comap_subtype_coe ht]
    have hst : e ⁻¹' t = s := Set.ext (fun x => (h x).symm)
    have hr := he.restrict_preimage ht
    rw [hst] at hr
    exact hr.map_eq

end General

end Maxwell.Continuum.Bloch
