import Maxwell.Continuum.ProfileSamplingTail
import Maxwell.Continuum.ProfileSampleEvaluation

/-! Rational DFT evaluation of the literal angular profile, with full sampling error. -/

set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open Maxwell.Certificate

noncomputable def realSampleCoefficient (grid : ℕ) [NeZero grid] (k : ℤ) : ℝ :=
  (grid : ℝ)⁻¹*∑ j : ZMod grid,
    angular (2*Real.pi*((j.val : ℝ)/grid))*Real.cos (2*Real.pi*(-(j.val : ℝ)*k/grid))

theorem realSampleCoefficient_eq (grid : ℕ) [NeZero grid] (k : ℤ) :
    realSampleCoefficient grid k = (PeriodicSampling.coefficient grid
      (fun j => ((angular (2*Real.pi*((j.val : ℝ)/grid)) : ℝ) : ℂ)) (k : ZMod grid)).re := by
  have hchar (j : ZMod grid) : ZMod.stdAddChar (-(j*(k : ZMod grid))) =
      Complex.exp (((2*Real.pi*(-(j.val : ℝ)*k/grid) : ℝ) : ℂ)*Complex.I) := by
    rw [show -(j*(k : ZMod grid)) = ((-k : ℤ) : ZMod grid)*j by push_cast; ring,
      ← PeriodicSampling.phase_grid]
    unfold PeriodicSampling.phase
    congr 1
    push_cast
    ring
  simp only [PeriodicSampling.coefficient, smul_eq_mul, hchar]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul,
    Complex.re_sum]
  unfold realSampleCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.exp_ofReal_mul_I_re]
  ring

def rationalSampleCoefficient (grid D P : ℕ) [NeZero grid] (k : ℤ) : ℚ :=
  (grid : ℚ)⁻¹*∑ j : ZMod grid,
    (angularApprox ((j.val : ℚ)/grid) P).center*
      (Calibration.cosTurnApprox (-(j.val : ℚ)*k/grid) (D+1) P).center

theorem grid_phase_bound (grid D : ℕ) [NeZero grid] (j : ZMod grid) (k : ℤ)
    (hk : |k| ≤ (D : ℤ)) : |-(j.val : ℚ)*k/grid| ≤ (D+1 : ℕ) := by
  have hq := grid_fraction_bound grid j
  have hkr : |(k : ℚ)| ≤ D := by exact_mod_cast hk
  calc
    _ = |(j.val : ℚ)/grid| * |(k : ℚ)| := by simp only [abs_div, abs_mul, abs_neg]; ring
    _ ≤ 1*(D : ℚ) := mul_le_mul hq hkr (abs_nonneg _) (by norm_num)
    _ ≤ _ := by push_cast; linarith

theorem profile_product_error {a b x y e : ℝ} (he : 0 ≤ e)
    (ha : |a-x| ≤ e) (hb : |b-y| ≤ e) (hx : |x| ≤ 2) (hb1 : |b| ≤ 1) :
    |a*b-x*y| ≤ 3*e := by
  calc
    _ = |(a-x)*b+x*(b-y)| := by congr 1; ring
    _ ≤ |a-x| * |b|+|x| * |b-y| := by simpa only [abs_mul] using abs_add_le ((a-x)*b) (x*(b-y))
    _ ≤ e*1+2*e := add_le_add
      (mul_le_mul ha hb1 (abs_nonneg _) he)
      (mul_le_mul hx hb (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem rationalSampleCoefficient_error (grid D P : ℕ) [NeZero grid] (k : ℤ)
    (hk : |k| ≤ (D : ℤ)) :
    |realSampleCoefficient grid k-(rationalSampleCoefficient grid D P k : ℝ)| ≤
      3*(1/2 : ℝ)^P := by
  have he (j : ZMod grid) :
      |angular (2*Real.pi*((j.val : ℝ)/grid))*Real.cos (2*Real.pi*(-(j.val : ℝ)*k/grid))-
      ((angularApprox ((j.val : ℚ)/grid) P).center : ℝ)*
      ((Calibration.cosTurnApprox (-(j.val : ℚ)*k/grid) (D+1) P).center : ℝ)| ≤
        3*(1/2 : ℝ)^P := by
    have ha := angularApprox_contains ((j.val : ℚ)/grid) P (grid_fraction_bound grid j)
    have hb := Calibration.cosTurnApprox_contains (-(j.val : ℚ)*k/grid) (D+1) P
      (grid_phase_bound grid D j k hk)
    rw [Ball.Contains, angularApprox_radius] at ha
    rw [Ball.Contains, Calibration.cosTurnApprox_radius] at hb
    push_cast at ha hb
    apply profile_product_error (by positivity) ha hb
    · exact_mod_cast angularApprox_center_bound ((j.val : ℚ)/grid) P (grid_fraction_bound grid j)
    · exact Real.abs_cos_le_one _
  unfold realSampleCoefficient rationalSampleCoefficient
  push_cast
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (grid : ℝ)⁻¹)]
  calc
    _ ≤ (grid : ℝ)⁻¹*∑ j : ZMod grid, |angular (2*Real.pi*((j.val : ℝ)/grid))*
      Real.cos (2*Real.pi*(-(j.val : ℝ)*k/grid))-
      ((angularApprox ((j.val : ℚ)/grid) P).center : ℝ)*
      ((Calibration.cosTurnApprox (-(j.val : ℚ)*k/grid) (D+1) P).center : ℝ)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (grid : ℝ)⁻¹*∑ _j : ZMod grid, 3*(1/2 : ℝ)^P := by
      gcongr with j _
      exact he j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (NeZero.ne (grid : ℝ)), one_mul]

theorem rationalSampleCoefficient_full_error (grid D P : ℕ) [NeZero grid] (k : ℤ)
    (hk : |k| ≤ (D : ℤ)) (hgrid : profileDegree P+D ≤ grid) :
    |(angularCoefficient 0 k).re-(rationalSampleCoefficient grid D P k : ℝ)| ≤
      4*(1/2 : ℝ)^P := by
  have hs := angular_sample_precision grid D P k hk hgrid
  have hr := (Complex.abs_re_le_norm
    (PeriodicSampling.coefficient grid
      (fun j => ((angular (2*Real.pi*((j.val : ℝ)/grid)) : ℝ) : ℂ)) (k : ZMod grid)-
      angularCoefficient 0 k)).trans hs
  rw [Complex.sub_re, ← realSampleCoefficient_eq] at hr
  have hq := rationalSampleCoefficient_error grid D P k hk
  have ht := abs_sub_le (angularCoefficient 0 k).re (realSampleCoefficient grid k)
    (rationalSampleCoefficient grid D P k : ℝ)
  rw [abs_sub_comm _ (realSampleCoefficient grid k)] at ht
  have hp : (1/2 : ℝ)^(P+100) ≤ (1/2 : ℝ)^P :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith

#print axioms realSampleCoefficient_eq
#print axioms rationalSampleCoefficient_full_error

end Maxwell.Continuum.Profile
