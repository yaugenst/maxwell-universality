import Maxwell.Continuum.CompactPositive
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Subtracting part of a normalized positive eigenprojection preserves
positivity and compactness. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum

open InnerProductSpace
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem rankOne_compact (u : H) : IsCompactOperator (rankOne ℂ u u) := by
  rw [rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ u)).comp_clm _

theorem positive_eigen_deflation (T : H →L[ℂ] H) (hT : T.IsPositive)
    (u : H) (hu : ‖u‖ = 1) (m a : ℝ) (he : T u = (m : ℂ) • u)
    (ha : a ≤ m) : (T - (a : ℂ) • rankOne ℂ u u).IsPositive := by
  let P := rankOne ℂ u u
  let J : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - P
  have hP : IsSelfAdjoint P := (isPositive_rankOne_self u).isSelfAdjoint
  have hJ : IsSelfAdjoint J := (ContinuousLinearMap.isPositive_id.isSelfAdjoint).sub hP
  have hii : inner ℂ u u = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; simp
  have him (x : H) : inner ℂ u (T x) = (m : ℂ) * inner ℂ u x := by
    rw [← hT.inner_left_eq_inner_right, he, inner_smul_left, Complex.conj_ofReal]
  have hjtj : J.comp (T.comp J) = T - (m : ℂ) • P := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [J, P, ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.id_apply, rankOne_apply, map_sub, map_smul,
      he, him, hii, smul_apply]
    module
  have hp : (T - (m : ℂ) • P).IsPositive := by
    have h := hT.conj_adjoint J
    rw [show ContinuousLinearMap.adjoint J = J from hJ, hjtj] at h
    exact h
  have hp' := (isPositive_rankOne_self u).smul_of_nonneg
    (show (0 : ℂ) ≤ ((m - a : ℝ) : ℂ) from Complex.zero_le_real.mpr (sub_nonneg.mpr ha))
  convert hp.add hp' using 1
  change T - (a : ℂ) • P = (T - (m : ℂ) • P) + ((m - a : ℝ) : ℂ) • P
  rw [Complex.ofReal_sub]
  module

omit [CompleteSpace H] in
theorem compact_eigen_deflation (T : H →L[ℂ] H) (hT : IsCompactOperator T)
    (u : H) (a : ℝ) : IsCompactOperator (T - (a : ℂ) • rankOne ℂ u u) :=
  hT.sub ((rankOne_compact u).smul (a : ℂ))

end Maxwell.Continuum
