import Maxwell.Continuum.WellPerronBounds
import Maxwell.Continuum.CompactDeflation

/-! A quantitative rank-one deflation whose actual scalar kernel remains
nonnegative. This is the source of the auxiliary well's spectral gap. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Well

open MeasureTheory InnerProductSpace

def gap : ℝ := FreeFiber.backgroundAmplitude / (2 : ℝ) ^ 88

theorem gap_pos : 0 < gap := by
  have h := FreeFiber.backgroundAmplitude_pos
  unfold gap
  positivity

theorem gap_le_mu : gap ≤ mu := by
  have h := mu_lower
  have hp := FreeFiber.backgroundAmplitude_pos
  unfold gap
  linarith

theorem topProfile_upper_numeric (x : Space) :
    topProfile x ≤ (2 : ℝ) ^ 32 * qw x := by
  apply (topProfile_upper x).trans
  apply mul_le_mul_of_nonneg_right _ (qw_nonneg x)
  apply (div_le_iff₀ mu_pos).mpr
  have h := mu_lower
  unfold kernelRowBound
  linarith

def gapOperator : ScalarL2 →L[ℂ] ScalarL2 :=
  physicalBirmanSchwinger - (gap : ℂ) • rankOne ℂ topVector topVector

theorem gapOperator_positive : gapOperator.IsPositive :=
  positive_eigen_deflation physicalBirmanSchwinger physicalBirmanSchwinger_positive
    topVector topVector_norm mu gap topVector_eigen gap_le_mu

theorem gapOperator_compact : IsCompactOperator gapOperator :=
  compact_eigen_deflation physicalBirmanSchwinger physicalBirmanSchwinger_compact topVector gap

theorem gapOperator_topVector : gapOperator topVector = ((mu - gap : ℝ) : ℂ) • topVector := by
  have hii : inner ℂ topVector topVector = 1 := by
    rw [inner_self_eq_norm_sq_to_K, topVector_norm]
    simp
  simp only [gapOperator, sub_apply, smul_apply, rankOne_apply, hii, one_smul,
    topVector_eigen, Complex.ofReal_sub, sub_smul]

def gapKernel (x y : Space) : ℝ := wellKernel x y - gap * topProfile x * topProfile y

theorem gapKernel_nonneg (x y : Space) (hne : x ≠ y) : 0 ≤ gapKernel x y := by
  by_cases hx : ‖x‖ < 1
  · by_cases hy : ‖y‖ < 1
    · have h := mul_le_mul (topProfile_upper_numeric x) (topProfile_upper_numeric y)
        (topProfile_nonneg y) (mul_nonneg (by positivity) (qw_nonneg x))
      have hm := mul_le_mul_of_nonneg_left h gap_pos.le
      have hk := wellKernel_lower x y hx.le hy.le hne
      unfold gapKernel gap at *
      nlinarith
    · rw [gapKernel, topProfile_supported y (le_of_not_gt hy), mul_zero, sub_zero]
      exact wellKernel_nonneg x y
  · rw [gapKernel, topProfile_supported x (le_of_not_gt hx), mul_zero, zero_mul, sub_zero]
    exact wellKernel_nonneg x y

theorem gapKernel_symm (x y : Space) : gapKernel x y = gapKernel y x := by
  rw [gapKernel, gapKernel, wellKernel_symm]
  ring

theorem profilePair_integrable (f : ScalarL2) :
    Integrable (fun y : Space => (topProfile y : ℂ) * f y) := by
  apply (L2.integrable_inner (𝕜 := ℂ) topVector f).congr
  filter_upwards [topVector_ae] with y hy
  rw [hy, RCLike.inner_apply, Complex.conj_ofReal]
  ring

theorem topVector_inner (f : ScalarL2) :
    inner ℂ topVector f = ∫ y : Space, (topProfile y : ℂ) * f y := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [topVector_ae] with y hy
  rw [hy, RCLike.inner_apply, Complex.conj_ofReal]
  ring

theorem gapKernel_integrand (f : ScalarL2) (x : Space) :
    Integrable (fun y : Space => (gapKernel x y : ℂ) * f y) := by
  convert (wellKernel_integrand f x).sub
    ((profilePair_integrable f).const_mul ((gap * topProfile x : ℝ) : ℂ)) using 1
  funext y
  simp only [gapKernel, Pi.sub_apply, Complex.ofReal_sub, Complex.ofReal_mul]
  ring

theorem gapOperator_kernel_ae (f : ScalarL2) :
    gapOperator f =ᵐ[volume] fun x => ∫ y : Space, (gapKernel x y : ℂ) * f y := by
  have he : gapOperator f = physicalBirmanSchwinger f -
      ((gap : ℂ) * inner ℂ topVector f) • topVector := by
    simp only [gapOperator, sub_apply, smul_apply, rankOne_apply, smul_smul]
  rw [he]
  filter_upwards [Lp.coeFn_sub (physicalBirmanSchwinger f)
      (((gap : ℂ) * inner ℂ topVector f) • topVector),
    Lp.coeFn_smul ((gap : ℂ) * inner ℂ topVector f) topVector,
    physicalBirmanSchwinger_kernel_ae f, topVector_ae] with x hs hm ht hu
  rw [hs]
  change physicalBirmanSchwinger f x - _ = _
  rw [hm]
  change physicalBirmanSchwinger f x - ((gap : ℂ) * inner ℂ topVector f) * topVector x = _
  rw [ht, hu, topVector_inner]
  have hi := (profilePair_integrable f).const_mul ((gap * topProfile x : ℝ) : ℂ)
  calc
    _ = (∫ y : Space, (wellKernel x y : ℂ) * f y) -
        ∫ y : Space, ((gap * topProfile x : ℝ) : ℂ) * ((topProfile y : ℂ) * f y) := by
      rw [integral_const_mul, Complex.ofReal_mul]
      ring
    _ = _ := by
      rw [← integral_sub (wellKernel_integrand f x) hi]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        simp only [gapKernel, Complex.ofReal_sub, Complex.ofReal_mul]
        ring)

def gapAction (f : ScalarL2) (x : Space) : ℝ := ∫ y : Space, gapKernel x y * ‖f y‖

theorem gapAction_integrable (f : ScalarL2) (x : Space) :
    Integrable (fun y : Space => gapKernel x y * ‖f y‖) := by
  apply ((gapKernel_integrand (absolute f) x).re).congr
  filter_upwards [absolute_ae f] with y hy
  rw [hy]
  simp

theorem gapAction_nonneg (f : ScalarL2) (x : Space) : 0 ≤ gapAction f x := by
  apply integral_nonneg_of_ae
  filter_upwards [volume.ae_ne x] with y hy
  exact mul_nonneg (gapKernel_nonneg x y (Ne.symm hy)) (norm_nonneg _)

theorem gapOperator_absolute_ae (f : ScalarL2) :
    gapOperator (absolute f) =ᵐ[volume] fun x => (gapAction f x : ℂ) := by
  filter_upwards [gapOperator_kernel_ae (absolute f)] with x hx
  rw [hx, gapAction, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [absolute_ae f] with y hy
  rw [hy, Complex.ofReal_mul]

theorem gapOperator_norm_ae (f : ScalarL2) :
    ∀ᵐ x, ‖gapOperator f x‖ ≤ gapAction f x := by
  filter_upwards [gapOperator_kernel_ae f] with x hx
  rw [hx]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [volume.ae_ne x] with y hy
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gapKernel_nonneg x y (Ne.symm hy))]

theorem gapOperator_absolute_energy (f : ScalarL2) :
    RCLike.re (inner ℂ f (gapOperator f)) ≤
      RCLike.re (inner ℂ (absolute f) (gapOperator (absolute f))) := by
  rw [L2.inner_def, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) _ _),
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) _ _)]
  apply integral_mono_ae (L2.integrable_inner (𝕜 := ℂ) _ _).re
    (L2.integrable_inner (𝕜 := ℂ) _ _).re
  filter_upwards [absolute_ae f, gapOperator_absolute_ae f, gapOperator_norm_ae f]
    with x hx ht hn
  rw [hx, ht, complex_inner_re_ofReal]
  exact (re_inner_le_norm (𝕜 := ℂ) _ _).trans
    (mul_le_mul_of_nonneg_left hn (norm_nonneg _))

end Maxwell.Continuum.Well
