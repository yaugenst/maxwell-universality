import Maxwell.Continuum.PeriodicPoleReflection
import Maxwell.Continuum.PeriodicPoleScaled

/-! The longitudinal derivative at the actual imaginary pole is purely
imaginary with strictly positive imaginary coefficient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open Auxiliary Set Metric Filter
open scoped Topology

attribute [local irreducible] coordinateBand dielectricBand imaginaryPole imaginaryRise

theorem coordinateBand_derivative_imaginary_re (j : Fin 3) {β : ℝ}
    (hβ : |β| < analyticRadius) :
    (deriv (coordinateBand j) ((β : ℂ) * Complex.I)).re = 0 := by
  have hc := (coordinateBand_analytic j ((β : ℂ) * Complex.I)
    (by simpa using hβ)).differentiableAt.hasDerivAt
  have hi := hc.comp (β : ℂ) ((hasDerivAt_id (β : ℂ)).mul_const Complex.I)
  have ho : IsOpen {x : ℝ | |x| < analyticRadius} :=
    isOpen_lt continuous_abs continuous_const
  have hr : ∀ᶠ x : ℝ in 𝓝 β,
      ((coordinateBand j ∘ fun w : ℂ => w * Complex.I) (x : ℂ)).im = 0 := by
    filter_upwards [ho.mem_nhds hβ] with x hx
    exact coordinateBand_imaginary_real j hx
  have hz := RealHolomorphicCoefficients.deriv_im_zero hi.differentiableAt hr
  rw [hi.deriv] at hz
  simpa only [one_mul, Complex.mul_I_im] using hz

theorem imaginaryRise_derivative_eq (j : Fin 3) {β : ℝ}
    (hβ : |β| < analyticRadius) :
    deriv (imaginaryRise j) β = (deriv (coordinateBand j) ((β : ℂ) * Complex.I)).im := by
  simpa only [Complex.mul_I_re, neg_neg] using (imaginaryRise_hasDerivAt j hβ).deriv

theorem imaginaryPole_longitudinal_re {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    (deriv (coordinateBand j) ((imaginaryPole D hh j : ℂ) * Complex.I)).re = 0 := by
  apply coordinateBand_derivative_imaginary_re j
  rw [abs_of_pos (imaginaryPole_pos D hh j)]
  exact (imaginaryPole_mem_small D hh j).2.trans_lt
    (lt_of_le_of_lt (imaginary_scale_bounds D.h_pos.le hh).1
      (by linarith [analyticRadius_pos]))

theorem imaginaryPole_longitudinal_im_pos {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    0 < (deriv (coordinateBand j) ((imaginaryPole D hh j : ℂ) * Complex.I)).im := by
  have hβ : |imaginaryPole D hh j| < analyticRadius := by
    rw [abs_of_pos (imaginaryPole_pos D hh j)]
    exact (imaginaryPole_mem_small D hh j).2.trans_lt
      (lt_of_le_of_lt (imaginary_scale_bounds D.h_pos.le hh).1
        (by linarith [analyticRadius_pos]))
  rw [← imaginaryRise_derivative_eq j hβ]
  exact imaginaryRise_deriv_pos D.h_pos hh j
    ⟨imaginaryPole_pos D hh j, imaginaryPole_lt_two_inverse_scale D hh j⟩

theorem imaginaryPole_longitudinal_derivative {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    ∃ c : ℝ, 0 < c ∧
      deriv (coordinateBand j) ((imaginaryPole D hh j : ℂ) * Complex.I) =
        (c : ℂ) * Complex.I := by
  refine ⟨_, imaginaryPole_longitudinal_im_pos D hh j, ?_⟩
  apply Complex.ext
  · simp only [Complex.mul_I_re, Complex.ofReal_im, neg_zero,
      imaginaryPole_longitudinal_re]
  · simp only [Complex.mul_I_im, Complex.ofReal_re]

end Maxwell.Continuum.PeriodicBand
