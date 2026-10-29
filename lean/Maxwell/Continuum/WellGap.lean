import Maxwell.Continuum.WellDeflation
import Maxwell.Continuum.CompactPositiveRayleigh

/-! The actual well eigenvalue is simple and has an explicit gap.
Compactness and the nonnegative deflated kernel give the complement norm bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Well

open MeasureTheory InnerProductSpace

theorem topProfile_pos_inside (x : Space) (hx : ‖x‖ < 1) : 0 < topProfile x := by
  have hq : 0 < qw x := by
    apply lt_of_le_of_ne (qw_nonneg x)
    intro h
    have hz := (qw_zero_iff x).mp h.symm
    linarith
  exact (mul_pos (by positivity : 0 < (1 : ℝ) / 2 ^ 29) hq).trans_le
    (topProfile_lower x)

theorem gapOperator_supported (f : ScalarL2) :
    ∀ᵐ x, 1 ≤ ‖x‖ → gapOperator f x = 0 := by
  filter_upwards [gapOperator_kernel_ae f] with x hx hnorm
  rw [hx]
  have hq := (qw_zero_iff x).mpr hnorm
  have hp := topProfile_supported x hnorm
  simp [gapKernel, wellKernel, hq, hp]

theorem nonnegative_supported_overlap_ne_zero (v : ScalarL2) (hvn : ‖v‖ = 1)
    (hv : ∀ᵐ x, v x = ((v x).re : ℂ) ∧ 0 ≤ (v x).re)
    (hs : ∀ᵐ x, 1 ≤ ‖x‖ → v x = 0) : inner ℂ topVector v ≠ 0 := by
  intro hz
  have hi : Integrable (fun x : Space => topProfile x * (v x).re) := by
    have h : Integrable (fun x : Space => ((topProfile x : ℂ) * v x).re) :=
      (profilePair_integrable v).re
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      using h
  have hn : 0 ≤ᵐ[volume] (fun x : Space => topProfile x * (v x).re) := by
    filter_upwards [hv] with x hx
    exact mul_nonneg (topProfile_nonneg x) hx.2
  have he : (∫ x : Space, topProfile x * (v x).re) = 0 := by
    have h : RCLike.re (inner ℂ topVector v) = 0 := congrArg RCLike.re hz
    rw [topVector_inner, ← integral_re (profilePair_integrable v)] at h
    change (∫ x : Space, ((topProfile x : ℂ) * v x).re) = 0 at h
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.zero_re] using h
  have ha := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp he
  have hvz : v = 0 := by
    apply Lp.ext
    filter_upwards [ha, hv, hs, Lp.coeFn_zero ℂ 2 (volume : Measure Space)]
      with x hx hr hsup hzero
    rw [hzero]
    change v x = 0
    by_cases hball : ‖x‖ < 1
    · have hrz : (v x).re = 0 := (mul_eq_zero.mp hx).resolve_left (topProfile_pos_inside x hball).ne'
      rw [hr.1, hrz, Complex.ofReal_zero]
    · exact hsup (le_of_not_gt hball)
  rw [hvz, norm_zero] at hvn
  norm_num at hvn

theorem gapOperator_norm : ‖gapOperator‖ ≤ mu - gap := by
  by_cases hz : gapOperator = 0
  · rw [hz, norm_zero]
    exact sub_nonneg.mpr gap_le_mu
  · let : Nontrivial ScalarL2 := nontrivial_of_ne rootVector 0 rootVector_ne_zero
    obtain ⟨v, hvn, hv⟩ := compactPositive_topEigenvector_after_improvement
      gapOperator gapOperator_compact gapOperator_positive hz absolute absolute_norm
      gapOperator_absolute_energy
    have hreal : ∀ᵐ x, absolute v x = ((absolute v x).re : ℂ) ∧ 0 ≤ (absolute v x).re := by
      filter_upwards [absolute_ae v] with x hx
      rw [hx]
      exact ⟨rfl, norm_nonneg _⟩
    have hsup : ∀ᵐ x, 1 ≤ ‖x‖ → absolute v x = 0 := by
      have hs := gapOperator_supported (absolute v)
      rw [hv] at hs
      filter_upwards [hs, Lp.coeFn_smul (‖gapOperator‖ : ℂ) (absolute v)] with x hx he hball
      have h := hx hball
      rw [he] at h
      change (‖gapOperator‖ : ℂ) * absolute v x = 0 at h
      exact (mul_eq_zero.mp h).resolve_left
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))
    have hin := nonnegative_supported_overlap_ne_zero (absolute v) hvn hreal hsup
    have hsym := gapOperator_positive.inner_left_eq_inner_right topVector (absolute v)
    rw [gapOperator_topVector, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at hsym
    have he := mul_right_cancel₀ hin hsym
    have he' : mu - gap = ‖gapOperator‖ := Complex.ofReal_injective he
    exact he'.symm.le

theorem well_complement_norm (f : ScalarL2) (hf : inner ℂ topVector f = 0) :
    ‖physicalBirmanSchwinger f‖ ≤ (mu - gap) * ‖f‖ := by
  have he : gapOperator f = physicalBirmanSchwinger f := by
    simp only [gapOperator, sub_apply, smul_apply, rankOne_apply, hf, zero_smul,
      smul_zero, sub_zero]
  rw [← he]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right gapOperator_norm (norm_nonneg _))

theorem gap_numeric : (1 / (2 : ℝ) ^ 190) ≤ gap := by
  norm_num [gap, FreeFiber.backgroundAmplitude]

theorem top_eigenvector_simple (f : ScalarL2)
    (hf : physicalBirmanSchwinger f = (mu : ℂ) • f) :
    f = (inner ℂ topVector f) • topVector := by
  let z := f - (inner ℂ topVector f) • topVector
  have hii : inner ℂ topVector topVector = 1 := by
    rw [inner_self_eq_norm_sq_to_K, topVector_norm]
    simp
  have hz : inner ℂ topVector z = 0 := by
    simp only [z, inner_sub_right, inner_smul_right, hii, mul_one, sub_self]
  have he : physicalBirmanSchwinger z = (mu : ℂ) • z := by
    simp only [z, map_sub, map_smul, hf, topVector_eigen, smul_sub]
    rw [smul_comm (inner ℂ topVector f) (mu : ℂ) topVector]
  have h := well_complement_norm z hz
  rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg mu_pos.le] at h
  have hzn : ‖z‖ = 0 := by nlinarith [norm_nonneg z, gap_pos]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzn)

theorem top_eigenvector_iff (f : ScalarL2) :
    physicalBirmanSchwinger f = (mu : ℂ) • f ↔
      ∃ c : ℂ, f = c • topVector := by
  constructor
  · intro h
    exact ⟨inner ℂ topVector f, top_eigenvector_simple f h⟩
  · rintro ⟨c, rfl⟩
    rw [map_smul, topVector_eigen, smul_comm]

end Maxwell.Continuum.Well
