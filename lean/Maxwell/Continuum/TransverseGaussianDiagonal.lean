import Maxwell.Continuum.TransverseGaussianAsymptotic
import Mathlib.MeasureTheory.Integral.Pi

/-! Exact normalization of the two-dimensional diagonal Gaussian. Coordinate
reflection symmetry gives this diagonal transverse quadratic form in the
selected-band application. -/

noncomputable section

namespace Maxwell.Continuum.TransverseGaussian

open MeasureTheory

def diagonalQuadratic (Q : Fin 2 → ℝ) (c : ℝ) (x : Plane) : ℝ :=
  (∑ j, Q j * (x j) ^ 2) / (2 * c)

theorem diagonal_gaussian_integral (Q : Fin 2 → ℝ) {T c : ℝ}
    (hQ : ∀ j, 0 < Q j) (hT : 0 < T) (hc : 0 < c) :
    (∫ x : Plane, Real.exp (-T * diagonalQuadratic Q c x)) =
      2 * Real.pi * c / (T * Real.sqrt (Q 0 * Q 1)) := by
  have h0 := hQ 0
  have h1 := hQ 1
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  have heq (x : Fin 2 → ℝ) :
      Real.exp (-T * diagonalQuadratic Q c (WithLp.toLp 2 x)) =
        ∏ j : Fin 2, Real.exp (-(T * Q j / (2 * c)) * x j ^ 2) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [diagonalQuadratic, Fin.sum_univ_two]
    ring
  simp_rw [heq]
  have hp := integral_fintype_prod_volume_eq_prod
    (fun j : Fin 2 => fun x : ℝ => Real.exp (-(T * Q j / (2 * c)) * x ^ 2))
  trans ∏ j : Fin 2, ∫ x : ℝ, Real.exp (-(T * Q j / (2 * c)) * x ^ 2)
  · convert! hp using 1
  simp_rw [integral_gaussian]
  rw [Fin.prod_univ_two]
  have hfrac : Real.pi / (T * Q 0 / (2 * c)) *
      (Real.pi / (T * Q 1 / (2 * c))) =
        (2 * Real.pi * c / T) ^ 2 / (Q 0 * Q 1) := by field_simp
  rw [← Real.sqrt_mul (by positivity : 0 ≤ Real.pi / (T * Q 0 / (2 * c))), hfrac,
    Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (by positivity)]
  ring

theorem diagonal_gaussian_complex_integral (Q : Fin 2 → ℝ) {T c : ℝ}
    (hQ : ∀ j, 0 < Q j) (hT : 0 < T) (hc : 0 < c) :
    (∫ x : Plane, gaussian T (diagonalQuadratic Q c x)) =
      ((2 * Real.pi * c / (T * Real.sqrt (Q 0 * Q 1)) : ℝ) : ℂ) := by
  change (∫ x : Plane, (Real.exp (-T * diagonalQuadratic Q c x) : ℂ)) = _
  rw [integral_complex_ofReal, diagonal_gaussian_integral Q hQ hT hc]

/-- The exact leading coefficient and a proved `T^(-3/2)` remainder. -/
theorem LocalData.diagonal_asymptotic (D : LocalData) (Q : Fin 2 → ℝ) {T c : ℝ}
    (hQ : ∀ j, 0 < Q j) (hT : 0 < T) (hc : 0 < c)
    (hquad : D.quadratic = diagonalQuadratic Q c) :
    ‖(∫ x in D.domain, D.amplitude x * wave T (D.phase x)) -
      D.center * ((2 * Real.pi * c / (T * Real.sqrt (Q 0 * Q 1)) : ℝ) : ℂ)‖ ≤
        D.errorConstant / (T * Real.sqrt T) := by
  have h := D.integral_error hT
  rw [hquad, diagonal_gaussian_complex_integral Q hQ hT hc] at h
  exact h

end Maxwell.Continuum.TransverseGaussian
