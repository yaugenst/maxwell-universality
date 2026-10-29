import Maxwell.Continuum.WellAbsolute
import Maxwell.Continuum.CompactPositive
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! An actual normalized nonnegative top eigenvector of the literal
well operator. The eigenpair is derived from compactness and positivity;
pointwise absolute values attain the same Rayleigh maximum. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Well

open MeasureTheory

def mu : ℝ := ‖physicalBirmanSchwinger‖

theorem mu_lower : FreeFiber.backgroundAmplitude / (2 : ℝ) ^ 27 ≤ mu :=
  physicalBirmanSchwinger_norm_lower

theorem mu_pos : 0 < mu := norm_pos_iff.mpr physicalBirmanSchwinger_ne_zero

theorem physicalBirmanSchwinger_positive : physicalBirmanSchwinger.IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨physicalBirmanSchwinger_selfAdjoint, ?_⟩
  intro u
  change 0 ≤ RCLike.re (inner ℂ (physicalBirmanSchwinger u) u)
  rw [inner_re_symm]
  exact physicalBirmanSchwinger_nonnegative u

theorem topEigenvector_exists :
    ∃ v : ScalarL2, ‖v‖ = 1 ∧ physicalBirmanSchwinger v = (mu : ℂ) • v := by
  let : Nontrivial ScalarL2 := nontrivial_of_ne rootVector 0 rootVector_ne_zero
  exact compactPositive_topEigenvector physicalBirmanSchwinger
    physicalBirmanSchwinger_compact physicalBirmanSchwinger_positive physicalBirmanSchwinger_ne_zero

theorem well_energy_upper (u : ScalarL2) :
    RCLike.re (inner ℂ u (physicalBirmanSchwinger u)) ≤ mu * ‖u‖ ^ 2 := by
  calc
    _ ≤ ‖u‖ * ‖physicalBirmanSchwinger u‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖u‖ * (‖physicalBirmanSchwinger‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = _ := by unfold mu; ring

theorem nonnegative_topEigenvector_exists :
    ∃ u : ScalarL2, ‖u‖ = 1 ∧ physicalBirmanSchwinger u = (mu : ℂ) • u ∧
      (∀ᵐ x, u x = ((u x).re : ℂ) ∧ 0 ≤ (u x).re) := by
  obtain ⟨v, hvnorm, hv⟩ := topEigenvector_exists
  have hanorm : ‖absolute v‖ = 1 := (absolute_norm v).trans hvnorm
  have hven : RCLike.re (inner ℂ v (physicalBirmanSchwinger v)) = mu := by
    rw [hv, inner_smul_right, inner_self_eq_norm_sq_to_K, hvnorm]
    simp
  have haen : RCLike.re (inner ℂ (absolute v) (physicalBirmanSchwinger (absolute v))) = mu := by
    apply le_antisymm
    · simpa only [hanorm, one_pow, mul_one] using well_energy_upper (absolute v)
    · rw [← hven]
      exact absolute_energy_ge v
  have hm : IsMaxOn physicalBirmanSchwinger.reApplyInnerSelf
      (Metric.sphere (0 : ScalarL2) ‖absolute v‖) (absolute v) := by
    intro z hz
    have hzn : ‖z‖ = 1 := by simpa only [hanorm, Metric.mem_sphere, dist_zero_right] using hz
    change RCLike.re (inner ℂ (physicalBirmanSchwinger z) z) ≤
      RCLike.re (inner ℂ (physicalBirmanSchwinger (absolute v)) (absolute v))
    rw [inner_re_symm (physicalBirmanSchwinger z) z,
      inner_re_symm (physicalBirmanSchwinger (absolute v)) (absolute v), haen]
    simpa only [hzn, one_pow, mul_one] using well_energy_upper z
  have hr : physicalBirmanSchwinger.rayleighQuotient (absolute v) = mu := by
    change RCLike.re (inner ℂ (physicalBirmanSchwinger (absolute v)) (absolute v)) /
      ‖absolute v‖ ^ 2 = mu
    rw [inner_re_symm, haen, hanorm]
    simp
  have he := physicalBirmanSchwinger_selfAdjoint.eq_smul_self_of_isLocalExtrOn
    (Or.inr hm.isLocalMaxOn)
  rw [hr] at he
  refine ⟨absolute v, hanorm, he, ?_⟩
  filter_upwards [absolute_ae v] with x hx
  rw [hx]
  exact ⟨rfl, norm_nonneg _⟩

def topVector : ScalarL2 := Classical.choose nonnegative_topEigenvector_exists

theorem topVector_norm : ‖topVector‖ = 1 :=
  (Classical.choose_spec nonnegative_topEigenvector_exists).1

theorem topVector_eigen : physicalBirmanSchwinger topVector = (mu : ℂ) • topVector :=
  (Classical.choose_spec nonnegative_topEigenvector_exists).2.1

theorem topVector_nonnegative :
    ∀ᵐ x, topVector x = ((topVector x).re : ℂ) ∧ 0 ≤ (topVector x).re :=
  (Classical.choose_spec nonnegative_topEigenvector_exists).2.2

end Maxwell.Continuum.Well
