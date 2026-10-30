import Maxwell.Continuum.CellSpatialTranslation
import Mathlib.Algebra.Module.ZLattice.Summable

/-! The actual three-dimensional cell lattice has summable fourth-power
distance tails. This supplies a summability theorem, not a finite truncation. -/

noncomputable section

namespace Maxwell.Continuum.CellGauge

open Bloch

theorem integerVector_injective : Function.Injective integerVector := by
  intro a b hab
  funext j
  have hj := congrArg (fun x : Space => x j) hab
  exact Int.cast_injective hj

theorem integerVector_sub (a b : Bloch.Alias) : integerVector (b-a) = integerVector b-integerVector a := by
  apply PiLp.ext
  intro j
  simp only [integerVector_apply, PiLp.sub_apply, Pi.sub_apply, Int.cast_sub]

theorem integerVector_sub_norm_pos {a b : Bloch.Alias} (hne : b ≠ a) :
    0 < ‖integerVector (b-a)‖ := by
  apply norm_pos_iff.mpr
  rw [integerVector_sub, sub_ne_zero]
  exact fun he => hne (integerVector_injective he)

theorem cellLattice_summable_inverse_four (a : Bloch.Alias) :
    Summable (fun b : Bloch.Alias => ‖integerVector (b-a)‖⁻¹^4) := by
  let B := PiLp.basisFun 2 ℝ (Fin 3)
  let Λ : Submodule ℤ Space := Submodule.span ℤ (Set.range B)
  have hm (b : Bloch.Alias) : integerVector b ∈ Λ := by
    apply (B.mem_span_iff_repr_mem ℤ _).mpr
    intro j
    exact ⟨b j, rfl⟩
  let inclusion : Bloch.Alias → Λ := fun b => ⟨integerVector b, hm b⟩
  have hi : Function.Injective inclusion := by
    intro b c hbc
    exact integerVector_injective (congrArg Subtype.val hbc)
  have hr : Module.finrank ℤ Λ = 3 := by
    rw [ZLattice.rank ℝ Λ]
    simp [Space]
  have hs := ZLattice.summable_norm_sub_inv_pow Λ 4 (by omega : Module.finrank ℤ Λ < 4)
    (integerVector a)
  exact (hs.comp_injective hi).congr fun b => by
    simp only [Function.comp_apply, inclusion, integerVector_sub]

#print axioms cellLattice_summable_inverse_four

end Maxwell.Continuum.CellGauge
