import Maxwell.Continuum.BlochPartition

/-! The exact cell/alias regrouping as an onto L² linear isometry, obtained
by composing representatives with the proved measure-preserving bijection. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory

set_option backward.isDefEq.respectTransparency false

section General

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- L² pullback by a proved measure-preserving equivalence, including its
explicit inverse pullback. -/
def measureEquivL2 (e : X ≃ᵐ Y) {μ : Measure X} {ν : Measure Y}
    (he : MeasurePreserving e μ ν) : Lp E 2 ν ≃ₗᵢ[ℂ] Lp E 2 μ where
  __ := Lp.compMeasurePreservingₗ ℂ e he
  invFun := Lp.compMeasurePreserving e.symm he.symm
  left_inv f := by
    change Lp.compMeasurePreserving e.symm he.symm
      (Lp.compMeasurePreserving e he f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f he he.symm]
    have hc : (e ∘ e.symm) = id := funext e.apply_symm_apply
    simpa only [hc] using Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change Lp.compMeasurePreserving e he
      (Lp.compMeasurePreserving e.symm he.symm f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f he.symm he]
    have hc : (e.symm ∘ e) = id := funext e.symm_apply_apply
    simpa only [hc] using Lp.compMeasurePreserving_id_apply f
  norm_map' f := Lp.norm_compMeasurePreserving f he

theorem measureEquivL2_ae (e : X ≃ᵐ Y) {μ : Measure X} {ν : Measure Y}
    (he : MeasurePreserving e μ ν) (f : Lp E 2 ν) :
    measureEquivL2 e he f =ᵐ[μ] (fun x => f (e x)) :=
  Lp.coeFn_compMeasurePreserving f he

end General

abbrev CellAliasL2 := Lp ℂ 2 (cellMeasure.prod (Measure.count : Measure Alias))
abbrev CellAliasFieldL2 := PiLp 2 (fun _ : Fin 3 => CellAliasL2)

/-- Literal regrouping of scalar Fourier space into all integer aliases. -/
def regroup : ScalarL2 ≃ₗᵢ[ℂ] CellAliasL2 :=
  measureEquivL2 join join_measurePreserving

theorem regroup_ae (f : ScalarL2) :
    regroup f =ᵐ[cellMeasure.prod Measure.count]
      (fun rn => f (integerVector rn.2 + (rn.1 : Space))) :=
  measureEquivL2_ae join join_measurePreserving f

/-- Componentwise Plancherel followed by the proved cell/alias regrouping. -/
def fourierRegroup : FieldL2 ≃ₗᵢ[ℂ] CellAliasFieldL2 :=
  fieldFourier.trans (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 3 => regroup))

theorem fourierRegroup_norm (u : FieldL2) : ‖fourierRegroup u‖ = ‖u‖ :=
  fourierRegroup.norm_map u

theorem fourierRegroup_inner (u v : FieldL2) :
    inner ℂ (fourierRegroup u) (fourierRegroup v) = inner ℂ u v :=
  fourierRegroup.inner_map_map u v

theorem fourierRegroup_ae (u : FieldL2) (i : Fin 3) :
    fourierRegroup u i =ᵐ[cellMeasure.prod Measure.count]
      (fun rn => fieldFourier u i (integerVector rn.2 + (rn.1 : Space))) :=
  regroup_ae (fieldFourier u i)

end Maxwell.Continuum.Bloch
