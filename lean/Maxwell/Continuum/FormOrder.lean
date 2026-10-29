import Maxwell.Continuum.FormPerturbation
import Mathlib.Tactic.Linarith

/-! Quadratic order estimates for bounded perturbations of a partial operator. -/

namespace Maxwell.Continuum.FormOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem energy (A : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) (x : A.domain) :
    (inner ℂ (x : H) (FormPerturbation.addBounded A B x)).re =
      (inner ℂ (x : H) (A x)).re + (inner ℂ (x : H) (B x)).re := by
  change (inner ℂ (x : H) (A x + B x)).re = _
  rw [inner_add_right, Complex.add_re]

theorem lower (A : H →ₗ.[ℂ] H) (B : H →L[ℂ] H) (K : ℝ)
    (hB : ∀ x : H, -K * ‖x‖ ^ 2 ≤ (inner ℂ x (B x)).re) (x : A.domain) :
    (inner ℂ (x : H) (A x)).re - K * ‖(x : H)‖ ^ 2 ≤
      (inner ℂ (x : H) (FormPerturbation.addBounded A B x)).re := by
  rw [energy]
  have h := hB x
  linarith

theorem shifted_order (A : H →ₗ.[ℂ] H) (B D : H →L[ℂ] H) (c : ℝ)
    (hBD : ∀ x : H, (inner ℂ x (D x)).re ≤ (inner ℂ x (B x)).re - c * ‖x‖ ^ 2)
    (x : A.domain) :
    (inner ℂ (x : H) (FormPerturbation.addBounded A D x)).re ≤
      (inner ℂ (x : H) (FormPerturbation.addBounded A B x)).re - c * ‖(x : H)‖ ^ 2 := by
  rw [energy, energy]
  have h := hBD x
  linarith

end Maxwell.Continuum.FormOrder
