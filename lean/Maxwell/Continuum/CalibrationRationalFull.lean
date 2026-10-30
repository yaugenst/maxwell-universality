import Maxwell.Continuum.CalibrationRationalCoordinates
import Maxwell.Continuum.CalibrationCentralInverse
import Maxwell.Continuum.CalibrationScaledFull

/-! Executable rational full-fiber Feshbach application. The only dense
inverse is the literal fixed 24-by-24 rational central matrix. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

def rationalComplementApply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (K : ℕ) (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  rationalInverseApply t E r (rationalNoncentral f) K

def rationalSourceApply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (K : ℕ) (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  f-rationalLeftCoupling (rationalComplementApply t E r K f)

def rationalLiftApply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (K : ℕ) (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  rationalCentral f-rationalComplementApply t E r K (rationalRightCoupling f)

def rationalFullApply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (K : ℕ) (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  rationalComplementApply t E r K f+rationalLiftApply t E r K
    (rationalCentralMatrixApply (rationalMatrixInverse (rationalSchurMatrix t E r K))
      (rationalSourceApply t E r K f))

theorem represents_complementApply (t E : ℚ) (r : Fin 3 → ℚ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (ht : (3 : ℝ) ≤ t ∧ (t : ℝ) ≤ 4)
    (hE : (7 : ℝ) ≤ E ∧ (E : ℝ) ≤ 8)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) (K : ℕ) :
    Represents (rationalComplementApply t E r K f)
      (scaledComplementApprox t E (fun j => (r j : ℝ)) hr ht hE K u) :=
  represents_inverseApply t E r hr ht.1 hE (represents_noncentral hf) K

theorem represents_sourceApply (t E : ℚ) (r : Fin 3 → ℚ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (ht : (3 : ℝ) ≤ t ∧ (t : ℝ) ≤ 4)
    (hE : (7 : ℝ) ≤ E ∧ (E : ℝ) ≤ 8)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) (K : ℕ) :
    Represents (rationalSourceApply t E r K f)
      (scaledSourceApprox t E (fun j => (r j : ℝ)) hr ht hE K u) :=
  represents_sub hf (represents_leftCoupling (represents_complementApply t E r hr ht hE hf K))

theorem represents_liftApply (t E : ℚ) (r : Fin 3 → ℚ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (ht : (3 : ℝ) ≤ t ∧ (t : ℝ) ≤ 4)
    (hE : (7 : ℝ) ≤ E ∧ (E : ℝ) ≤ 8)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) (K : ℕ) :
    Represents (rationalLiftApply t E r K f)
      (scaledLiftApprox t E (fun j => (r j : ℝ)) hr ht hE K u) :=
  represents_sub (represents_central hf)
    (represents_complementApply t E r hr ht hE (represents_rightCoupling hf) K)

theorem represents_fullApply (t E : ℚ) (r : Fin 3 → ℚ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (ht : (3 : ℝ) ≤ t ∧ (t : ℝ) ≤ 4)
    (hE : (7 : ℝ) ≤ E ∧ (E : ℝ) ≤ 8)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) (K : ℕ)
    (hS : IsUnit (scaledFiniteSchurApprox t E (fun j => (r j : ℝ)) hr ht hE K)) :
    Represents (rationalFullApply t E r K f)
      (scaledFullApprox t E (fun j => (r j : ℝ)) hr ht hE K u) := by
  have hc := represents_complementApply t E r hr ht hE hf K
  have hx := represents_sourceApply t E r hr ht hE hf K
  have hj := rationalCentralMatrixApply_represents
    (rationalMatrixInverse (rationalSchurMatrix t E r K)) hx
  rw [rationalSchurInverse_sound t E r hr ht hE K hS] at hj
  have hid (v : FiberSpace) :
      (centralFinUnitary (centralFinOperator (Ring.inverse
        (scaledFiniteSchurApprox t E (fun j => (r j : ℝ)) hr ht hE K))
          (centralFinUnitary.symm (centralProjectionToSpace v)))).val =
      extendCentral (Ring.inverse (scaledFiniteSchurApprox t E (fun j => (r j : ℝ)) hr ht hE K)) v := by
    change (centralFinUnitary (centralFinUnitary.symm ((Ring.inverse
      (scaledFiniteSchurApprox t E (fun j => (r j : ℝ)) hr ht hE K))
        (centralFinUnitary (centralFinUnitary.symm (centralProjectionToSpace v)))))).val = _
    rw [LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [hid] at hj
  have hl := represents_liftApply t E r hr ht hE hj K
  intro ν j
  change rationalComplexLinear (rationalComplementApply t E r K f ν j+
    rationalLiftApply t E r K _ ν j) = _
  rw [map_add]
  change rationalComplexValue (rationalComplementApply t E r K f ν j)+
    rationalComplexValue (rationalLiftApply t E r K _ ν j) = _
  rw [hc,hl]
  rfl

#print axioms represents_fullApply

end Maxwell.Continuum.Calibration
