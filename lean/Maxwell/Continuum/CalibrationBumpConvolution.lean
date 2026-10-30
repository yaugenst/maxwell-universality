import Maxwell.Continuum.CalibrationTorusConvolution

/-! The actual certified rational bump polynomial, transported through
the full Fourier unitary, is a finite convolution with its computed
coefficients and its derived alias support and error bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open FreeFiber CellBandFourier PeriodicSampling

def computedRootConvolution (s : ℚ) (N ell : ℕ) : FiberSpace →L[ℂ] FiberSpace :=
  finiteAliasConvolution (rootDegree s N ell) (fun n => rectangleCenter (computedRootCoefficient s N ell n))

theorem computedRootPolynomial_eq_finite (s : ℚ) (N ell : ℕ) :
    computedRootPolynomial s N ell = finiteTorusPolynomial (rootDegree s N ell)
      (fun n => rectangleCenter (computedRootCoefficient s N ell n)) := by
  apply ContinuousMap.ext
  intro x
  rw [computedRootPolynomial_apply, finiteTorusPolynomial_apply]
  rfl

theorem computedRootConvolution_eq (s : ℚ) (N ell : ℕ) :
    computedRootConvolution s N ell = aliasMultiplier (computedRootPolynomial s N ell) := by
  rw [computedRootPolynomial_eq_finite, finiteTorusPolynomial_convolution]
  rfl

theorem computedRootConvolution_error (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell) :
    ‖aliasMultiplier (rootTorus s hs)-computedRootConvolution s N ell‖ ≤ (1/2 : ℝ)^N := by
  rw [computedRootConvolution_eq]
  change ‖aliasMultiplierCLM (rootTorus s hs)-aliasMultiplierCLM (computedRootPolynomial s N ell)‖ ≤ _
  rw [← map_sub]
  exact (aliasMultiplier_norm _).trans (computedRootPolynomial_norm_error s hs N ell hlog)

theorem computedRootConvolution_norm (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell) : ‖computedRootConvolution s N ell‖ ≤ 2 := by
  rw [computedRootConvolution_eq]
  exact (aliasMultiplier_norm _).trans (computedRootPolynomial_norm s hs N ell hlog)

theorem computedRootConvolution_supported (s : ℚ) (N ell : ℕ)
    {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R) :
    AliasSupported (computedRootConvolution s N ell u) (R+rootDegree s N ell) :=
  hu.finiteConvolution _ _

#print axioms computedRootConvolution_error
#print axioms computedRootConvolution_supported

end Maxwell.Continuum.Calibration
