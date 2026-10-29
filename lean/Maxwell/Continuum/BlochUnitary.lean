import Maxwell.Continuum.BlochUnfiber

/-! The actual unitary Bloch transform into L² of the infinite alias Hilbert space. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency false

theorem toFiberL2_add (v w : QuasiAliasFieldL2) :
    toFiberL2 (v + w) = toFiberL2 v + toFiberL2 w := by
  apply Lp.ext
  have ha := ae_all_iff.mpr (fun i : Fin 3 =>
    product_ae_all_alias (Lp.coeFn_add (v i) (w i)))
  filter_upwards [toFiberL2_coordinate_ae (v + w), toFiberL2_coordinate_ae v,
    toFiberL2_coordinate_ae w, Lp.coeFn_add (toFiberL2 v) (toFiberL2 w), ha]
      with q hvw hv hw hsum ha
  rw [hsum]
  apply lp.ext
  funext n
  apply PiLp.ext
  intro i
  change toFiberL2 (v + w) q n i = toFiberL2 v q n i + toFiberL2 w q n i
  rw [hvw, hv, hw]
  exact ha i n

theorem toFiberL2_smul (c : ℂ) (v : QuasiAliasFieldL2) :
    toFiberL2 (c • v) = c • toFiberL2 v := by
  apply Lp.ext
  have ha := ae_all_iff.mpr (fun i : Fin 3 =>
    product_ae_all_alias (Lp.coeFn_smul c (v i)))
  filter_upwards [toFiberL2_coordinate_ae (c • v), toFiberL2_coordinate_ae v,
    Lp.coeFn_smul c (toFiberL2 v), ha] with q hcv hv hsmul ha
  rw [hsmul]
  apply lp.ext
  funext n
  apply PiLp.ext
  intro i
  change toFiberL2 (c • v) q n i = c * toFiberL2 v q n i
  rw [hcv, hv]
  exact ha i n

def fiberIsometry : QuasiAliasFieldL2 →ₗᵢ[ℂ] FiberL2 where
  toFun := toFiberL2
  map_add' := toFiberL2_add
  map_smul' := toFiberL2_smul
  norm_map' := toFiberL2_norm

/-- Surjectivity follows from the explicit ungrouping of each component. -/
def fiberEquiv : QuasiAliasFieldL2 ≃ₗᵢ[ℂ] FiberL2 :=
  LinearIsometryEquiv.ofSurjective fiberIsometry
    (fun w => ⟨fromFiberL2 w, toFiberL2_fromFiberL2 w⟩)

@[simp] theorem fiberEquiv_apply (v : QuasiAliasFieldL2) : fiberEquiv v = toFiberL2 v := rfl

theorem fromFiberL2_toFiberL2 (v : QuasiAliasFieldL2) : fromFiberL2 (toFiberL2 v) = v := by
  apply fiberEquiv.injective
  exact toFiberL2_fromFiberL2 (toFiberL2 v)

/-- The literal Fourier transform, lattice partition, Jacobian, and Hilbert-valued
Fubini map, composed into an onto complex-linear isometry. -/
def unitary : FieldL2 ≃ₗᵢ[ℂ] FiberL2 := quasiTransform.trans fiberEquiv

theorem unitary_norm (u : FieldL2) : ‖unitary u‖ = ‖u‖ := unitary.norm_map u

theorem unitary_inner (u v : FieldL2) : inner ℂ (unitary u) (unitary v) = inner ℂ u v :=
  unitary.inner_map_map u v

theorem unitary_coordinate_ae (u : FieldL2) :
    ∀ᵐ q ∂quasiMeasure, ∀ n : Alias, ∀ i : Fin 3,
      unitary u q n i = fieldFourier u i (quasiFrequencyJoin (q, n)) := by
  have h := ae_all_iff.mpr (fun i : Fin 3 => product_ae_all_alias (quasiTransform_ae u i))
  filter_upwards [toFiberL2_coordinate_ae (quasiTransform u), h] with q hq hi
  intro n i
  exact (hq n i).trans (hi i n)

end Maxwell.Continuum.Bloch
