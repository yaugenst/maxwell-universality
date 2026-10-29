import Maxwell.Green.PhysicalAnalytic
import Mathlib.Algebra.Order.ToIntervalMod

/-! Periodicity transports a conventional-cell complex spectral exclusion
from a cube centered at any real momentum to all real momenta. -/

namespace Maxwell.Green.CenteredExclusion

open Maxwell.Spectral Maxwell.Spectral.Lattice
open PhysicalAnalytic

noncomputable section

/-- The genuine complex conventional operator is periodic under every
integer combination of its three angular periods. -/
theorem operator_integer_periodic (material : Cell20 → ℝ)
    (n : Fin 3 → ℤ) (z : ComplexTorusCoordinates) :
    ConventionalAnalytic.operator material
      (z + ∑ i, n i • ((2 * Real.pi : ℂ) • Pi.single i 1)) =
        ConventionalAnalytic.operator material z := by
  have hp : ∀ s : Finset (Fin 3), Function.Periodic (ConventionalAnalytic.operator material)
      (∑ i ∈ s, n i • ((2 * Real.pi : ℂ) • Pi.single i 1)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Function.Periodic]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hi : Function.Periodic (ConventionalAnalytic.operator material)
          ((2 * Real.pi : ℂ) • Pi.single i 1) := operator_periodic material i
      exact (hi.zsmul (n i)).add_period ih
  exact hp Finset.univ z

/-- A centered angular representative, with the actual integer period
relating it to the requested real momentum. -/
theorem exists_centered_representative (θ q : RealTorusCoordinates) :
    ∃ r ∈ torusCube (-Real.pi) (2 * Real.pi), ∃ n : Fin 3 → ℤ,
      complexifyCoordinates q = complexifyCoordinates θ + complexifyCoordinates r +
        ∑ i, n i • ((2 * Real.pi : ℂ) • Pi.single i 1) := by
  let hp : 0 < 2 * Real.pi := by positivity
  let r : RealTorusCoordinates := fun i => toIcoMod hp (-Real.pi) (q i - θ i)
  let n : Fin 3 → ℤ := fun i => toIcoDiv hp (-Real.pi) (q i - θ i)
  refine ⟨r, ?_, n, ?_⟩
  · intro i
    have h := toIcoMod_mem_Ico hp (-Real.pi) (q i - θ i)
    exact ⟨h.1, h.2.le⟩
  · ext i
    have hr := toIcoMod_add_toIcoDiv_zsmul hp (-Real.pi) (q i - θ i)
    change r i + n i • (2 * Real.pi) = q i - θ i at hr
    have hc := congrArg Complex.ofReal hr
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_zsmul] at hc
    simp only [complexifyCoordinates, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      Pi.single_apply]
    simp only [smul_eq_mul, zsmul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [zsmul_eq_mul] at hc
    push_cast at hc
    linear_combination -hc

/-- Invertibility throughout a centered angular cube implies invertibility
at every real momentum with the same arbitrary complex displacement. -/
theorem centered_invertible_all (material : Cell20 → ℝ) (E : ℝ)
    (θ : RealTorusCoordinates) (w : ComplexTorusCoordinates)
    (hI : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
      (shiftedOperator material E
        (complexifyCoordinates θ + complexifyCoordinates q + w)).IsInvertible) :
    ∀ q : RealTorusCoordinates,
      (shiftedOperator material E (complexifyCoordinates q + w)).IsInvertible := by
  intro q
  obtain ⟨r, hr, n, hn⟩ := exists_centered_representative θ q
  have he : shiftedOperator material E (complexifyCoordinates q + w) =
      shiftedOperator material E (complexifyCoordinates θ + complexifyCoordinates r + w) := by
    unfold shiftedOperator
    rw [hn]
    rw [add_right_comm _ _ w, operator_integer_periodic]
  rw [he]
  exact hI r hr

end
end Maxwell.Green.CenteredExclusion
