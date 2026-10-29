import Maxwell.Continuum.CompactPositive
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! Equality in the operator-norm Rayleigh bound produces an actual
eigenvector; norm-preserving energy improvements preserve top eigenvectors. -/

noncomputable section

namespace Maxwell.Continuum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem positive_norm_energy_upper (T : H →L[ℂ] H) (u : H) :
    RCLike.re (inner ℂ u (T u)) ≤ ‖T‖ * ‖u‖ ^ 2 := by
  calc
    _ ≤ ‖u‖ * ‖T u‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖u‖ * (‖T‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = _ := by ring

theorem eigen_of_norm_energy (T : H →L[ℂ] H) (hs : IsSelfAdjoint T)
    (u : H) (hu : ‖u‖ = 1) (he : RCLike.re (inner ℂ u (T u)) = ‖T‖) :
    T u = (‖T‖ : ℂ) • u := by
  have hm : IsMaxOn T.reApplyInnerSelf (Metric.sphere (0 : H) ‖u‖) u := by
    intro z hz
    have hzn : ‖z‖ = 1 := by simpa only [hu, Metric.mem_sphere, dist_zero_right] using hz
    change RCLike.re (inner ℂ (T z) z) ≤ RCLike.re (inner ℂ (T u) u)
    rw [inner_re_symm (T z) z, inner_re_symm (T u) u, he]
    simpa only [hzn, one_pow, mul_one] using positive_norm_energy_upper T z
  have hr : T.rayleighQuotient u = ‖T‖ := by
    change RCLike.re (inner ℂ (T u) u) / ‖u‖ ^ 2 = ‖T‖
    rw [inner_re_symm, he, hu]
    simp
  have h := hs.eq_smul_self_of_isLocalExtrOn (Or.inr hm.isLocalMaxOn)
  rwa [hr] at h

theorem compactPositive_topEigenvector_after_improvement [Nontrivial H]
    (T : H →L[ℂ] H) (hc : IsCompactOperator T) (hp : T.IsPositive) (hne : T ≠ 0)
    (a : H → H) (han : ∀ v, ‖a v‖ = ‖v‖)
    (hae : ∀ v, RCLike.re (inner ℂ v (T v)) ≤ RCLike.re (inner ℂ (a v) (T (a v)))) :
    ∃ v : H, ‖a v‖ = 1 ∧ T (a v) = (‖T‖ : ℂ) • a v := by
  obtain ⟨v, hvn, hv⟩ := compactPositive_topEigenvector T hc hp hne
  have hn : ‖a v‖ = 1 := (han v).trans hvn
  refine ⟨v, hn, eigen_of_norm_energy T hp.isSelfAdjoint (a v) hn ?_⟩
  apply le_antisymm
  · simpa only [hn, one_pow, mul_one] using positive_norm_energy_upper T (a v)
  · have hvE : RCLike.re (inner ℂ v (T v)) = ‖T‖ := by
      rw [hv, inner_smul_right, inner_self_eq_norm_sq_to_K, hvn]
      simp
    rw [← hvE]
    exact hae v

end Maxwell.Continuum
