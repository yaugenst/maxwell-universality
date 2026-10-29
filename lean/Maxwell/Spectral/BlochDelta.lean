import Maxwell.Spectral.Bloch

/-!
# Bloch transform of a lattice delta

A source supported on one actual lattice edge becomes a single conventional
cell component with the negative Fourier character of its cell translate.
-/

namespace Maxwell.Spectral.Bloch

open MeasureTheory Maxwell.Spectral.Lattice
open scoped ENNReal

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem scalarFourier_single (n : Site) (a : ℂ) :
    scalarFourier (lp.single 2 n a) = a • UnitAddTorus.mFourierLp 2 (-n) := by
  rw [← UnitAddTorus.coe_mFourierBasis]
  apply UnitAddTorus.mFourierBasis.repr.injective
  rw [map_smul, HilbertBasis.repr_self]
  ext k
  simp [scalarFourier_coefficients, lp.single_apply, Pi.single_apply,
    neg_eq_iff_eq_neg, smul_eq_mul]

theorem componentSequence_single (e : Edge) (a : ℂ) (r : Edge20) :
    componentSequence (lp.single 2 e a) r =
      if r = (edgeCellEquiv e).1 then lp.single 2 (edgeCellEquiv e).2 a else 0 := by
  ext n
  simp only [componentSequence_apply, lp.single_apply]
  by_cases hr : r = (edgeCellEquiv e).1
  · rw [ite_eq_left hr]
    simp only [lp.single_apply, Pi.single_apply]
    congr 1
    apply propext
    constructor
    · intro h
      have hh := congrArg edgeCellEquiv h
      simp only [Equiv.apply_symm_apply] at hh
      exact congrArg Prod.snd hh
    · intro h
      apply edgeCellEquiv.injective
      rw [Equiv.apply_symm_apply]
      exact Prod.ext hr h
  · rw [ite_eq_right hr]
    rw [Pi.single_eq_of_ne]
    · rfl
    · intro h
      apply hr
      have hh := congrArg edgeCellEquiv h
      simp only [Equiv.apply_symm_apply] at hh
      exact congrArg Prod.fst hh

theorem transform_single_component (e : Edge) (a : ℂ) (r : Edge20) :
    transform (lp.single 2 e a) r =
      if r = (edgeCellEquiv e).1 then
        a • UnitAddTorus.mFourierLp 2 (-(edgeCellEquiv e).2) else 0 := by
  rw [transform_component, componentSequence_single]
  split_ifs <;> simp only [scalarFourier_single, map_zero]

theorem transform_single_component_ae (e : Edge) (a : ℂ) (r : Edge20) :
    transform (lp.single 2 e a) r =ᵐ[volume] fun t =>
      if r = (edgeCellEquiv e).1 then
        a * UnitAddTorus.mFourier (-(edgeCellEquiv e).2) t else 0 := by
  rw [transform_single_component]
  split_ifs with hr
  · filter_upwards [Lp.coeFn_smul a (UnitAddTorus.mFourierLp 2 (-(edgeCellEquiv e).2)),
      UnitAddTorus.coeFn_mFourierLp 2 (-(edgeCellEquiv e).2)] with t hs hf
    simp only [hs, Pi.smul_apply, hf, smul_eq_mul]
  · exact Lp.coeFn_zero ℂ 2 volume

end
end Maxwell.Spectral.Bloch
