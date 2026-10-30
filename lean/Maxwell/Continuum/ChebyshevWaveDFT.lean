import Maxwell.Continuum.ChebyshevWaveSampling
import Maxwell.Continuum.ChebyshevWaveEvaluation

/-! Executable rational sampling of the actual plane-wave Chebyshev coefficients. -/

namespace Maxwell.Continuum.Profile

open Maxwell.Certificate Calibration

theorem rectangleCenter_mul (a b : ComplexRectangle) :
    rectangleCenter (a.mul b) = rectangleCenter a*rectangleCenter b := by
  simp only [rectangleCenter, ComplexRectangle.mul, Ball.mul, Ball.add, Ball.neg]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

def waveProductSample (grid : ℕ) [NeZero grid] (q : ℚ) (Q P : ℕ)
    (n : ℤ) (j : ZMod grid) : ComplexRectangle :=
  (gridCharacterApprox grid P (-(j*(n : ZMod grid)))).mul
    (waveSample q Q P (gridTurn grid j))

def rationalWaveCoefficient (grid : ℕ) [NeZero grid] (q : ℚ) (Q P : ℕ)
    (n : ℤ) : ComplexRectangle :=
  ComplexRectangle.point
    ((grid : ℚ)⁻¹*∑ j : ZMod grid, (waveProductSample grid q Q P n j).re.center)
    ((grid : ℚ)⁻¹*∑ j : ZMod grid, (waveProductSample grid q Q P n j).im.center)

theorem rationalWaveCoefficient_center (grid : ℕ) [NeZero grid] (q : ℚ) (Q P : ℕ)
    (n : ℤ) :
    rectangleCenter (rationalWaveCoefficient grid q Q P n) =
      (grid : ℂ)⁻¹*∑ j : ZMod grid,
        rectangleCenter (gridCharacterApprox grid P (-(j*(n : ZMod grid))))*
        rectangleCenter (waveSample q Q P (gridTurn grid j)) := by
  simp_rw [← rectangleCenter_mul]
  change rectangleCenter (rationalWaveCoefficient grid q Q P n) =
    (grid : ℂ)⁻¹*∑ j : ZMod grid, rectangleCenter (waveProductSample grid q Q P n j)
  simp only [rationalWaveCoefficient, rectangleCenter, ComplexRectangle.point]
  push_cast
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

theorem wave_product_error {a b x y : ℂ} {δ : ℝ} (hδ : 0≤δ)
    (ha : ‖a-x‖≤2*δ) (hb : ‖b-y‖≤2*δ) (hx : ‖x‖≤3) (hb1 : ‖b‖≤1) :
    ‖a*b-x*y‖≤8*δ := by
  calc
    _ = ‖(a-x)*b+x*(b-y)‖ := by congr 1; ring
    _ ≤ ‖a-x‖*‖b‖+‖x‖*‖b-y‖ := by simpa only [norm_mul] using norm_add_le ((a-x)*b) (x*(b-y))
    _ ≤ (2*δ)*1+3*(2*δ) := add_le_add
      (mul_le_mul ha hb1 (norm_nonneg _) (by positivity))
      (mul_le_mul hx hb (norm_nonneg _) (by norm_num))
    _ = _ := by ring

theorem rationalWaveCoefficient_error (grid : ℕ) [NeZero grid] (q : ℚ) (Q P : ℕ)
    (hq : |q|≤Q) (n : ℤ) :
    ‖PeriodicSampling.coefficient grid
      (fun j => waveAngular (2*Real.pi*(q : ℝ)) (2*Real.pi*((j.val : ℝ)/grid))) (n : ZMod grid)-
      rectangleCenter (rationalWaveCoefficient grid q Q P n)‖ ≤ 8*(1/2 : ℝ)^P := by
  have he (j : ZMod grid) :
      ‖ZMod.stdAddChar (-(j*(n : ZMod grid)))*
          waveAngular (2*Real.pi*(q : ℝ)) (2*Real.pi*((j.val : ℝ)/grid))-
        rectangleCenter (gridCharacterApprox grid P (-(j*(n : ZMod grid))))*
          rectangleCenter (waveSample q Q P (gridTurn grid j))‖ ≤ 8*(1/2 : ℝ)^P := by
    have hc := gridCharacterApprox_error grid P (-(j*(n : ZMod grid)))
    have hw := waveSample_error q (gridTurn grid j) Q P hq (gridTurn_bound grid j)
    simp only [gridTurn, Rat.cast_div, Rat.cast_natCast] at hw
    apply wave_product_error (by positivity) hc hw
    · have ht := norm_sub_le_norm_sub_add_norm_sub (rectangleCenter (gridCharacterApprox grid P (-(j*(n : ZMod grid)))))
        (ZMod.stdAddChar (-(j*(n : ZMod grid)))) 0
      simp only [sub_zero] at ht
      rw [norm_sub_rev (rectangleCenter _) (ZMod.stdAddChar _)] at ht
      have hp : (1/2 : ℝ)^P≤1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hn : ‖(ZMod.stdAddChar (-(j*(n : ZMod grid))) : ℂ)‖=1 := by simp
      rw [hn] at ht
      linarith
    · exact (waveAngular_norm _ _).le
  rw [rationalWaveCoefficient_center]
  simp only [PeriodicSampling.coefficient, smul_eq_mul, ← mul_sub, ← Finset.sum_sub_distrib, norm_mul]
  rw [norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (grid : ℝ)⁻¹*∑ j : ZMod grid,
        ‖ZMod.stdAddChar (-(j*(n : ZMod grid)))*
          waveAngular (2*Real.pi*(q : ℝ)) (2*Real.pi*((j.val : ℝ)/grid))-
        rectangleCenter (gridCharacterApprox grid P (-(j*(n : ZMod grid))))*
          rectangleCenter (waveSample q Q P (gridTurn grid j))‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (grid : ℝ)⁻¹*∑ _j : ZMod grid, 8*(1/2 : ℝ)^P := by
      gcongr with j _
      exact he j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (NeZero.ne (grid : ℝ)), one_mul]

theorem rationalWaveCoefficient_full_error (grid D K P : ℕ) [NeZero grid]
    (q : ℚ) (Q : ℕ) (hq : |q|≤Q) (hk : |2*Real.pi*(q : ℝ)|≤K)
    (n : ℤ) (hn : |n|≤(D : ℤ)) (hgrid : waveDegree K P+D≤grid) :
    ‖waveCoefficient (2*Real.pi*(q : ℝ)) n-
      rectangleCenter (rationalWaveCoefficient grid q Q P n)‖ ≤ 9*(1/2 : ℝ)^P := by
  have hs := wave_sample_precision grid D K P hk n hn hgrid
  have hr := rationalWaveCoefficient_error grid q Q P hq n
  have ht := norm_sub_le_norm_sub_add_norm_sub (waveCoefficient (2*Real.pi*(q : ℝ)) n)
    (PeriodicSampling.coefficient grid
      (fun j => waveAngular (2*Real.pi*(q : ℝ)) (2*Real.pi*((j.val : ℝ)/grid))) (n : ZMod grid))
    (rectangleCenter (rationalWaveCoefficient grid q Q P n))
  rw [norm_sub_rev _ (PeriodicSampling.coefficient _ _ _)] at ht
  have hp : (1/2 : ℝ)^(P+100)≤(1/2 : ℝ)^P :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith

#print axioms rationalWaveCoefficient_full_error

end Maxwell.Continuum.Profile
