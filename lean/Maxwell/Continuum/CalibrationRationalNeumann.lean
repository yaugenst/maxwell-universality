import Maxwell.Continuum.CalibrationRationalStencil
import Maxwell.Continuum.CalibrationNeumannRounding
import Maxwell.Continuum.CalibrationAliasSupport

/-! An executable finite rational recurrence for the full complementary
Neumann inverse, with exact semantic equality and finite alias propagation.
Each update can be evaluated once on the enlarged finite alias array. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

def rationalInverseApply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (f : Alias → Fin 3 → V) : ℕ → Alias → Fin 3 → V
  | 0 => 0
  | K+1 => fun ν j => rationalFreeApply t E r f ν j-
      rationalFreeApply t E r (rationalPerturbation (rationalInverseApply t E r f K)) ν j

theorem represents_inverseApply (t E : ℚ) (r : Fin 3 → ℚ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (ht : (3 : ℝ) ≤ t) (hE : (7 : ℝ) ≤ E ∧ (E : ℝ) ≤ 8)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) (K : ℕ) :
    Represents (rationalInverseApply t E r f K)
      (Neumann.inverseApprox (scaledFreeInverse t E (fun j => (r j : ℝ)) hr ht hE)
        calibrationMaterialPerturbation K u) := by
  induction K with
  | zero =>
    intro ν j
    simp only [rationalInverseApply, Neumann.inverseApprox, Neumann.partialSeries,
      Finset.range_zero, Finset.sum_empty, mul_zero, zero_apply]
    change rationalComplexLinear 0 = 0
    exact map_zero _
  | succ K ih =>
    have hR := represents_freeApply t E r hr ht hE hf
    have hRB := represents_freeApply t E r hr ht hE (represents_perturbation ih)
    intro ν j
    rw [Neumann.inverseApprox_left_recurrence]
    change rationalComplexLinear (rationalFreeApply t E r f ν j-
      rationalFreeApply t E r (rationalPerturbation (rationalInverseApply t E r f K)) ν j) = _
    rw [map_sub]
    change rationalComplexValue (rationalFreeApply t E r f ν j)-
      rationalComplexValue (rationalFreeApply t E r (rationalPerturbation (rationalInverseApply t E r f K)) ν j) = _
    rw [hR, hRB]
    rfl

theorem AliasSupported.scaledFree {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R)
    (t E : ℝ) (r : Fin 3 → ℝ) (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t) (hE : 7 ≤ E ∧ E ≤ 8) :
    AliasSupported (scaledFreeInverse t E r hr ht hE u) R := by
  intro ν hν
  change scaledFreeInverseBlock t E r ν (u ν) = 0
  rw [hu ν hν, map_zero]

theorem scaledInverseApprox_supported (t E : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t) (hE : 7 ≤ E ∧ E ≤ 8)
    {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R) (K : ℕ) :
    AliasSupported (Neumann.inverseApprox (scaledFreeInverse t E r hr ht hE)
      calibrationMaterialPerturbation K u) (R+K) := by
  induction K with
  | zero =>
    simp only [Neumann.inverseApprox, Neumann.partialSeries, Finset.range_zero,
      Finset.sum_empty, mul_zero, zero_apply]
    exact AliasSupported.zero _
  | succ K ih =>
    rw [Neumann.inverseApprox_left_recurrence]
    change AliasSupported (scaledFreeInverse t E r hr ht hE u-
      scaledFreeInverse t E r hr ht hE (calibrationMaterialPerturbation
        (Neumann.inverseApprox (scaledFreeInverse t E r hr ht hE) calibrationMaterialPerturbation K u))) _
    have hf := (hu.scaledFree t E r hr ht hE).mono (by omega : R ≤ R+(K+1))
    have hg := (ih.materialPerturbation.scaledFree t E r hr ht hE).smul (-1)
    simpa only [neg_one_smul, sub_eq_add_neg, Nat.add_assoc] using hf.add hg

#print axioms represents_inverseApply
#print axioms scaledInverseApprox_supported

end Maxwell.Continuum.Calibration
