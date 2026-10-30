import Maxwell.Continuum.CalibrationRationalCentral
import Maxwell.Continuum.CalibrationRationalNeumann

/-! The executable rational Schur recurrence represents the literal
24-mode restriction of the infinite Maxwell fiber. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

def rationalSchurApply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (K : ℕ) (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  rationalCentralMaterial t E r f-rationalLeftCoupling
    (rationalInverseApply t E r (rationalNoncentral (rationalRightCoupling f)) K)

theorem represents_schurApply (t E : ℚ) (r : Fin 3 → ℚ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (ht : (3 : ℝ) ≤ t ∧ (t : ℝ) ≤ 4)
    (hE : (7 : ℝ) ≤ E ∧ (E : ℝ) ≤ 8)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) (K : ℕ) :
    Represents (rationalSchurApply t E r K f)
      (scaledSchurApprox t E (fun j => (r j : ℝ)) hr ht hE K u) := by
  exact represents_sub (represents_centralMaterial t E r hr ht hE hf)
    (represents_leftCoupling (represents_inverseApply t E r hr ht.1 hE
      (represents_noncentral (represents_rightCoupling hf)) K))

#print axioms represents_schurApply

end Maxwell.Continuum.Calibration
