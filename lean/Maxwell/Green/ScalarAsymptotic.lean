import Maxwell.Green.LocalResidue
import Maxwell.Green.SmoothRemainder
import Maxwell.Green.Rates

/-! Scalar Green asymptotics for the actual local pole and regular integrals.
The hypotheses concern local Taylor data and ordinary derivatives; neither
the pole asymptotic nor the decay of the regular integral is assumed. -/

noncomputable section

namespace Maxwell.Green

open MeasureTheory Filter Real Complex
open scoped Topology

/-- Ordinary normal derivative data for a compactly supported regular
integrand. The second derivative is integrable in all three variables. -/
structure RegularNormalData where
  amplitude : ℂ → ℝ → ℂ
  first : ℂ → ℝ → ℂ
  second : ℂ → ℝ → ℂ
  measurable : Measurable (Function.uncurry amplitude)
  derivative : ∀ w u, HasDerivAt (amplitude w) (first w u) u
  derivative_first : ∀ w u, HasDerivAt (first w) (second w u) u
  continuous_second : ∀ w, Continuous (second w)
  compact : ∀ w, HasCompactSupport (amplitude w)
  integrable_second : Integrable (Function.uncurry second)

namespace RegularNormalData

variable (R : RegularNormalData)

def normalIntegral (T : ℝ) (w : ℂ) : ℂ :=
  ∫ u : ℝ, Complex.exp (I * (T : ℂ) * u) * R.amplitude w u

def derivativeMass : ℝ := ∫ w : ℂ, ∫ u : ℝ, ‖R.second w u‖

theorem derivativeMass_nonneg : 0 ≤ R.derivativeMass :=
  integral_nonneg (fun _ => integral_nonneg (fun _ => norm_nonneg _))

theorem normalIntegral_measurable (T : ℝ) : Measurable (R.normalIntegral T) := by
  have hm : Measurable (fun z : ℂ × ℝ =>
      Complex.exp (I * (T : ℂ) * z.2) * R.amplitude z.1 z.2) := by
    have := R.measurable
    change Measurable (fun z : ℂ × ℝ => R.amplitude z.1 z.2) at this
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Two integrations by parts in the actual regular normal integral,
followed by integration over the transverse plane. -/
theorem integral_bound {T : ℝ} (hT : 0 < T) :
    Integrable (R.normalIntegral T) ∧
    ‖∫ w : ℂ, R.normalIntegral T w‖ ≤ R.derivativeMass / T ^ 2 := by
  have hb (w : ℂ) : ‖R.normalIntegral T w‖ ≤ (∫ u : ℝ, ‖R.second w u‖) / T ^ 2 :=
    compact_support_fourier_bound (R.amplitude w) (R.first w) (R.second w)
      (R.derivative w) (R.derivative_first w) (R.continuous_second w) (R.compact w) hT
  have hmajor : Integrable (fun w : ℂ => (∫ u : ℝ, ‖R.second w u‖) / T ^ 2) :=
    R.integrable_second.norm.integral_prod_left.div_const _
  have hi : Integrable (R.normalIntegral T) := hmajor.mono'
    (R.normalIntegral_measurable T).aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ w : ℂ, ‖R.normalIntegral T w‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℂ, (∫ u : ℝ, ‖R.second w u‖) / T ^ 2 :=
      integral_mono_ae hi.norm hmajor (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_div]; rfl

end RegularNormalData

/-- Sum of the actual localized pole and regular iterated integrals. -/
def localGreenIntegral (D : LocalSaddleData) (R : RegularNormalData) (ρ T : ℝ) : ℂ :=
  (∫ w : ℂ, ∫ u : ℝ, D.localizedPoleKernel ρ T w u) +
    ∫ w : ℂ, ∫ u : ℝ, Complex.exp (I * (T : ℂ) * u) * R.amplitude w u

theorem localGreenIntegral_asymptotic (D : LocalSaddleData) (R : RegularNormalData)
    {ρ : ℝ} (hρ : 0 < ρ) (hs : HasCompactSupport D.cutoff)
    (hp : ∀ w, D.cutoff w ≠ 0 → ‖D.phase w‖ ≤ ρ / 2)
    {v q₁ q₂ : ℝ} (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hmodel : D.model = quadraticPhase v q₁ q₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ‖localGreenIntegral D R ρ T - (2 * π : ℂ) * I * (D.amplitude0 *
        ((2 * π * v / (T * sqrt (q₁ * q₂)) : ℝ) : ℂ))‖ ≤
        C * T ^ (-(3 : ℝ) / 2) := by
  obtain ⟨C, hC, hbound⟩ := localized_pole_transverse_saddle_of_compact D hρ hs hp
    hv hq₁ hq₂ hmodel
  refine ⟨C + R.derivativeMass, add_nonneg hC R.derivativeMass_nonneg, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with T hTbound hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hreg := (R.integral_bound hTpos).2
  have hscale : R.derivativeMass / T ^ 2 ≤ R.derivativeMass * T ^ (-(3 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le hT (by norm_num : -(2 : ℝ) ≤ -(3 : ℝ) / 2)
    rw [Real.rpow_neg hTpos.le, Real.rpow_two] at h
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h R.derivativeMass_nonneg
  unfold localGreenIntegral
  rw [add_sub_right_comm]
  exact (norm_add_le _ _).trans ((add_le_add hTbound (hreg.trans hscale)).trans_eq (by ring))

/-- Fourier normalization and the conversion from normal frequency to
physical distance. -/
def normalizedLocalGreen (D : LocalSaddleData) (R : RegularNormalData)
    (ρ ν d : ℝ) : ℂ := ((2 * π : ℂ) ^ 3)⁻¹ * localGreenIntegral D R ρ (ν * d)

def scalarLeadingCoefficient (D : LocalSaddleData) (v q₁ q₂ ν : ℝ) : ℂ :=
  ((2 * π : ℂ) ^ 3)⁻¹ * ((2 * π : ℂ) * I * (D.amplitude0 *
    ((2 * π * v / (ν * sqrt (q₁ * q₂)) : ℝ) : ℂ)))

theorem normalizedLocalGreen_asymptotic (D : LocalSaddleData) (R : RegularNormalData)
    {ρ ν : ℝ} (hρ : 0 < ρ) (hν : 0 < ν) (hs : HasCompactSupport D.cutoff)
    (hp : ∀ w, D.cutoff w ≠ 0 → ‖D.phase w‖ ≤ ρ / 2)
    {v q₁ q₂ : ℝ} (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hmodel : D.model = quadraticPhase v q₁ q₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ d : ℝ in atTop,
      ‖normalizedLocalGreen D R ρ ν d - scalarLeadingCoefficient D v q₁ q₂ ν / (d : ℂ)‖ ≤
        C * d ^ (-(3 : ℝ) / 2) := by
  obtain ⟨C, hC, hbound⟩ := localGreenIntegral_asymptotic D R hρ hs hp hv hq₁ hq₂ hmodel
  refine ⟨‖((2 * π : ℂ) ^ 3)⁻¹‖ * C * ν ^ (-(3 : ℝ) / 2), by positivity, ?_⟩
  have ht : Tendsto (fun d : ℝ => ν * d) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hν).mpr tendsto_id
  filter_upwards [ht.eventually hbound, eventually_gt_atTop (0 : ℝ)] with d hb hd
  have heq : normalizedLocalGreen D R ρ ν d - scalarLeadingCoefficient D v q₁ q₂ ν / (d : ℂ) =
      ((2 * π : ℂ) ^ 3)⁻¹ * (localGreenIntegral D R ρ (ν * d) -
        (2 * π : ℂ) * I * (D.amplitude0 *
          ((2 * π * v / ((ν * d) * sqrt (q₁ * q₂)) : ℝ) : ℂ))) := by
    unfold normalizedLocalGreen scalarLeadingCoefficient
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, norm_mul]
  calc
    _ ≤ ‖((2 * π : ℂ) ^ 3)⁻¹‖ * (C * (ν * d) ^ (-(3 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by rw [Real.mul_rpow hν.le hd.le]; ring

def scalarShiftFactor (θ σ d : ℝ) : ℂ := Complex.exp (I * (θ : ℂ) * d - (σ : ℂ) * d)

def scalarLocalGreen (D : LocalSaddleData) (R : RegularNormalData)
    (ρ ν θ σ d : ℝ) : ℂ := scalarShiftFactor θ σ d * normalizedLocalGreen D R ρ ν d

theorem norm_scalarShiftFactor (θ σ d : ℝ) : ‖scalarShiftFactor θ σ d‖ = Real.exp (-σ * d) := by
  simp [scalarShiftFactor, Complex.norm_exp, Complex.mul_re, Complex.mul_im, neg_mul]

theorem scalarLocalGreen_asymptotic (D : LocalSaddleData) (R : RegularNormalData)
    {ρ ν : ℝ} (hρ : 0 < ρ) (hν : 0 < ν) (hs : HasCompactSupport D.cutoff)
    (hp : ∀ w, D.cutoff w ≠ 0 → ‖D.phase w‖ ≤ ρ / 2)
    {v q₁ q₂ : ℝ} (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hmodel : D.model = quadraticPhase v q₁ q₂) (θ σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ d : ℝ in atTop,
      ‖scalarLocalGreen D R ρ ν θ σ d - scalarShiftFactor θ σ d *
        (scalarLeadingCoefficient D v q₁ q₂ ν / (d : ℂ))‖ ≤
        Real.exp (-σ * d) * (C * d ^ (-(3 : ℝ) / 2)) := by
  obtain ⟨C, hC, hb⟩ := normalizedLocalGreen_asymptotic D R hρ hν hs hp hv hq₁ hq₂ hmodel
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with d hd
  rw [scalarLocalGreen, ← mul_sub, norm_mul, norm_scalarShiftFactor]
  exact mul_le_mul_of_nonneg_left hd (Real.exp_nonneg _)

theorem scalarLeadingCoefficient_ne_zero (D : LocalSaddleData)
    {v q₁ q₂ ν : ℝ} (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hν : 0 < ν)
    (ha : D.amplitude0 ≠ 0) : scalarLeadingCoefficient D v q₁ q₂ ν ≠ 0 := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : 0 < 2 * π * v / (ν * sqrt (q₁ * q₂)) := by positivity
  have hc' : ((2 * π * v / (ν * sqrt (q₁ * q₂)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hc.ne'
  dsimp [scalarLeadingCoefficient]
  exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero hπ)))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hπ) Complex.I_ne_zero)
      (mul_ne_zero ha hc'))

/-- For the scalar Green residue `-i/v`, Fourier normalization leaves the
positive determinant coefficient `1/(2πν√(q₁q₂))`. -/
theorem scalarLeadingCoefficient_of_normal_residue (D : LocalSaddleData)
    {v q₁ q₂ ν : ℝ} (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hν : 0 < ν)
    (ha : D.amplitude0 = -I / (v : ℂ)) :
    scalarLeadingCoefficient D v q₁ q₂ ν =
      ((1 / (2 * π * ν * sqrt (q₁ * q₂)) : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hv' : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hν' : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hν.ne'
  have hq' : ((sqrt (q₁ * q₂) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos hq₁ hq₂)).ne'
  unfold scalarLeadingCoefficient
  rw [ha]
  push_cast
  field_simp
  simp [Complex.I_sq]

/-- A nonzero residue coefficient yields every strict exponential lower
rate for the actual scalar local Green integral. -/
theorem eventually_scalarLocalGreen_exp_lower (D : LocalSaddleData) (R : RegularNormalData)
    {ρ ν : ℝ} (hρ : 0 < ρ) (hν : 0 < ν) (hs : HasCompactSupport D.cutoff)
    (hp : ∀ w, D.cutoff w ≠ 0 → ‖D.phase w‖ ≤ ρ / 2)
    {v q₁ q₂ : ℝ} (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hmodel : D.model = quadraticPhase v q₁ q₂) (ha : D.amplitude0 ≠ 0)
    (θ σ J : ℝ) (hσJ : σ < J) :
    ∀ᶠ d : ℝ in atTop, Real.exp (-J * d) ≤ ‖scalarLocalGreen D R ρ ν θ σ d‖ := by
  let c := ‖scalarLeadingCoefficient D v q₁ q₂ ν‖
  have hc : 0 < c := norm_pos_iff.mpr (scalarLeadingCoefficient_ne_zero D hv hq₁ hq₂ hν ha)
  obtain ⟨C, hC, hb⟩ := normalizedLocalGreen_asymptotic D R hρ hν hs hp hv hq₁ hq₂ hmodel
  have he := eventually_polynomial_remainder_small (c / 2) C 1 ((3 : ℝ) / 2)
    (by positivity) (by norm_num)
  have hexp := eventually_exp_le_polynomial_exp (c / 2) 1 σ J (by positivity) hσJ
  filter_upwards [hb, he, hexp, eventually_gt_atTop (0 : ℝ)] with d hd he hexp hdpos
  simp only [Real.rpow_one] at he hexp
  have hpow : C * d ^ (-(3 : ℝ) / 2) = |C| / d ^ ((3 : ℝ) / 2) := by
    rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
      Real.rpow_neg hdpos.le, abs_of_nonneg hC]
    exact (div_eq_mul_inv C _).symm
  have herr : ‖normalizedLocalGreen D R ρ ν d -
      scalarLeadingCoefficient D v q₁ q₂ ν / (d : ℂ)‖ ≤ (c / 2) / d := by
    rw [hpow] at hd
    exact hd.trans he
  have hlead : ‖scalarLeadingCoefficient D v q₁ q₂ ν / (d : ℂ)‖ = c / d := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdpos]
  have hnorm := norm_le_norm_sub_add (scalarLeadingCoefficient D v q₁ q₂ ν / (d : ℂ))
    (normalizedLocalGreen D R ρ ν d)
  rw [hlead, norm_sub_rev] at hnorm
  have hlower : (c / 2) / d ≤ ‖normalizedLocalGreen D R ρ ν d‖ := by
    have heq : c / d = 2 * ((c / 2) / d) := by ring
    linarith
  rw [scalarLocalGreen, norm_mul, norm_scalarShiftFactor]
  exact hexp.trans (by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hlower (Real.exp_nonneg _))

/-- Integer lattice distances give the geometric lower-rate form used in
the placement reduction. -/
theorem eventually_scalarLocalGreen_geometric_lower (D : LocalSaddleData) (R : RegularNormalData)
    {ρ ν : ℝ} (hρ : 0 < ρ) (hν : 0 < ν) (hs : HasCompactSupport D.cutoff)
    (hp : ∀ w, D.cutoff w ≠ 0 → ‖D.phase w‖ ≤ ρ / 2)
    {v q₁ q₂ : ℝ} (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hmodel : D.model = quadraticPhase v q₁ q₂) (ha : D.amplitude0 ≠ 0)
    (θ σ a : ℝ) (ha₀ : 0 < a) (haσ : a < Real.exp (-σ)) :
    ∀ᶠ n : ℕ in atTop, a ^ n ≤ ‖scalarLocalGreen D R ρ ν θ σ n‖ := by
  have hσ : σ < -Real.log a := by
    have h := Real.log_lt_log ha₀ haσ
    rw [Real.log_exp] at h
    linarith
  have h := tendsto_natCast_atTop_atTop.eventually
    (eventually_scalarLocalGreen_exp_lower D R hρ hν hs hp hv hq₁ hq₂ hmodel ha θ σ
      (-Real.log a) hσ)
  simpa only [neg_neg, Real.exp_mul, Real.exp_log ha₀, Real.rpow_natCast] using h

end Maxwell.Green
