import Maxwell.Continuum.CalibrationBumpPolynomial
import Maxwell.Continuum.CellGaugeBasic

/-! The finite rational Fourier polynomial approximates literal
multiplication on the full torus L² space in operator norm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open CellBandFourier MeasureTheory

def torusMultiplier (f : C(Torus, ℂ)) : CellFieldL2 →L[ℂ] CellFieldL2 :=
  DiagonalMap.diagonal (CompactCoefficient.multiplier (μ := torusMeasure) id measurable_id f)

theorem torusMultiplier_ae (f : C(Torus, ℂ)) (u : CellFieldL2) (j : Fin 3) :
    torusMultiplier f u j =ᵐ[torusMeasure] fun x => f x*u j x :=
  CompactCoefficient.multiplier_ae id measurable_id f (u j)

theorem torusMultiplier_norm (f : C(Torus, ℂ)) : ‖torusMultiplier f‖ ≤ ‖f‖ :=
  (DiagonalMap.diagonal_norm_le _).trans (CompactCoefficient.multiplier_norm_le id measurable_id f)

theorem torusMultiplier_sub (f g : C(Torus, ℂ)) :
    torusMultiplier (f-g) = torusMultiplier f-torusMultiplier g := by
  change DiagonalMap.diagonalCLM (CompactCoefficient.coefficientMap (μ := torusMeasure) id measurable_id (f-g)) =
    DiagonalMap.diagonalCLM (CompactCoefficient.coefficientMap (μ := torusMeasure) id measurable_id f)-
    DiagonalMap.diagonalCLM (CompactCoefficient.coefficientMap (μ := torusMeasure) id measurable_id g)
  rw [map_sub, map_sub]

def rootMultiplier (s : ℝ) (hs : 4 ≤ s) : CellFieldL2 →L[ℂ] CellFieldL2 :=
  torusMultiplier (rootTorus s hs)

def computedRootMultiplier (s : ℚ) (N ell : ℕ) : CellFieldL2 →L[ℂ] CellFieldL2 :=
  torusMultiplier (computedRootPolynomial s N ell)

theorem rootMultiplier_norm (s : ℝ) (hs : 4 ≤ s) : ‖rootMultiplier s hs‖ ≤ 1 :=
  (torusMultiplier_norm _).trans ((ContinuousMap.norm_le _ zero_le_one).mpr (rootTorus_norm_le_one s hs))

theorem computedRootMultiplier_norm (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell) : ‖computedRootMultiplier s N ell‖ ≤ 2 :=
  (torusMultiplier_norm _).trans (computedRootPolynomial_norm s hs N ell hlog)

theorem computedRootMultiplier_error (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell) :
    ‖rootMultiplier s hs-computedRootMultiplier s N ell‖ ≤ (1/2 : ℝ)^N := by
  change ‖torusMultiplier (rootTorus s hs)-torusMultiplier (computedRootPolynomial s N ell)‖ ≤ _
  rw [← torusMultiplier_sub]
  exact (torusMultiplier_norm _).trans (computedRootPolynomial_norm_error s hs N ell hlog)

#print axioms torusMultiplier_ae
#print axioms computedRootMultiplier_error

end Maxwell.Continuum.Calibration
