import Maxwell.Continuum.RealHolomorphicCoefficients

/-! An even holomorphic function that is real on a real neighborhood is
real on the imaginary diameter of its disk of analyticity. -/

noncomputable section

namespace Maxwell.Continuum.EvenTaylor

open Set Metric Filter
open scoped Topology

theorem imaginary_even_power (x : ℝ) (n : ℕ) :
    ((x : ℂ) * Complex.I) ^ (2 * n) = (((-x^2 : ℝ) : ℂ)) ^ n := by
  rw [pow_mul]
  congr 1
  rw [mul_pow, Complex.I_sq]
  push_cast
  ring

theorem imaginary_im_zero {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (hR : 0 < R)
    (heven : (fun z => f (-z)) =ᶠ[𝓝 0] f)
    (hreal : ∀ᶠ x : ℝ in 𝓝 0, (f (x : ℂ)).im = 0)
    {x : ℝ} (hx : |x| < R) : (f ((x : ℂ) * Complex.I)).im = 0 := by
  have ha : AnalyticAt ℂ f 0 := hf 0 (by simpa using hR)
  have hc (n : ℕ) : (coefficient f n).im = 0 :=
    RealHolomorphicCoefficients.coefficient_im_zero ha hreal n
  have hz : ‖(x : ℂ) * Complex.I‖ < R := by simpa using hx
  have hs := Complex.hasSum_im (hasSum_even_coefficients hf heven hz)
  have ht (n : ℕ) :
      (coefficient f (2 * n) * ((x : ℂ) * Complex.I)^(2*n)).im = 0 := by
    rw [imaginary_even_power, ← Complex.ofReal_pow]
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, hc,
      mul_zero, zero_mul, add_zero]
  have hzero : HasSum (fun _ : ℕ => (0 : ℝ)) (f ((x : ℂ) * Complex.I)).im := by
    simpa only [ht] using hs
  exact hzero.unique hasSum_zero

end Maxwell.Continuum.EvenTaylor
