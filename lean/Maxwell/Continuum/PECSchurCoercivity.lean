import Maxwell.Continuum.PECSchur

/-! The high free modes retain a fixed coercivity margin after gradient
elimination. No search for the next free eigenvalue is required. -/

noncomputable section

namespace Maxwell.Continuum

set_option backward.isDefEq.respectTransparency false

namespace GradientSchur

variable {G T : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup T] [InnerProductSpace ℂ T] [CompleteSpace T]

theorem boundedPart_lower_exact (B : G →L[ℂ] G)
    (hB : CoerciveInverse.Coercive B 1) (D : T →L[ℂ] T)
    (hD : ∀ x : T, (inner ℂ x (D x)).re ≤ 25 * ‖x‖ ^ 2)
    (E : T →L[ℂ] G) (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) (x : T) :
    -(25 + ell) * ‖x‖ ^ 2 ≤ (inner ℂ x (boundedPart B hB D E ell hell x)).re := by
  rw [boundedPart_energy]
  have hp := gradientInverse_nonnegative B hB ell hell (E x)
  have hd := hD x
  nlinarith

end GradientSchur

open TopologicalSpace

namespace ScalarDielectric

variable (ε : ScalarDielectric) (Ω : Opens Space)

theorem transverseSchurPart_lower_exact (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell)
    (x : transverseSpace Ω) :
    -(25 + ell) * ‖x‖ ^ 2 ≤ (inner ℂ x (ε.transverseSchurPart Ω ell hell x)).re :=
  GradientSchur.boundedPart_lower_exact (G := gradientSpace Ω) (T := transverseSpace Ω)
    _ _ _ (ε.transverseMaterial_upper Ω) _ _ _ x

theorem schurOperator_lower_exact (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell)
    (u : (transverseCurlCurl Ω).domain) :
    (inner ℂ (u : transverseSpace Ω) (transverseCurlCurl Ω u)).re -
      (25 + ell) * ‖(u : transverseSpace Ω)‖ ^ 2 ≤
        (inner ℂ (u : transverseSpace Ω) (ε.schurOperator Ω ell hell u)).re :=
  FormOrder.lower (H := transverseSpace Ω) (transverseCurlCurl Ω)
    (ε.transverseSchurPart Ω ell hell) (25 + ell)
    (ε.transverseSchurPart_lower_exact Ω ell hell) u

/-- The high-mode cutoff 26 leaves the uniform margin 3/4 throughout the
whole detuning window. -/
theorem schurOperator_high_coercive (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell)
    (hell' : ell ≤ 1 / 4) (u : (transverseCurlCurl Ω).domain)
    (hhigh : 26 * ‖(u : transverseSpace Ω)‖ ^ 2 ≤
      (inner ℂ (u : transverseSpace Ω) (transverseCurlCurl Ω u)).re) :
    (3 / 4 : ℝ) * ‖(u : transverseSpace Ω)‖ ^ 2 ≤
      (inner ℂ (u : transverseSpace Ω) (ε.schurOperator Ω ell hell u)).re := by
  have h := ε.schurOperator_lower_exact Ω ell hell u
  have he := mul_le_mul_of_nonneg_right hell' (sq_nonneg ‖(u : transverseSpace Ω)‖)
  nlinarith

end ScalarDielectric

end Maxwell.Continuum
