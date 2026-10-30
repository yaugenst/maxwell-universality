import Maxwell.Continuum.CalibrationArrayIndex

/-! A literal array implementation of the finite Neumann application.
Every layer is materialized once. Zero extension at the array boundary
is proved harmless from the actual alias-support theorem. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

def cachedInverseApply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ) (f : Alias → Fin 3 → V) : ℕ → Vector V (aliasArraySize B)
  | 0 => sampleAliasArray B 0
  | K+1 =>
    let previous := cachedInverseApply t E r B f K
    sampleAliasArray B (rationalFreeApply t E r f-
      rationalFreeApply t E r (rationalPerturbation (extendAliasArray B previous)))

theorem represents_sample_extend {f : RationalAliasField} {u : FiberSpace}
    (hf : Represents f u) (B : ℕ) (hu : AliasSupported u B) :
    Represents (extendAliasArray B (sampleAliasArray B f)) u := by
  intro ν j
  rw [extend_sample_alias]
  by_cases hν : aliasInCube B ν
  · simp only [hν, ↓reduceIte]
    exact hf ν j
  · have hout : ∃ k, (B : ℤ) < |ν k| := by
      simpa only [aliasInCube, not_forall, not_le] using hν
    rw [hu ν hout]
    simp only [hν, ↓reduceIte]
    exact map_zero rationalComplexLinear

theorem cachedInverseApply_sound (t E : ℚ) (r : Fin 3 → ℚ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (ht : (3 : ℝ) ≤ t) (hE : (7 : ℝ) ≤ E ∧ (E : ℝ) ≤ 8)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) {R : ℕ} (hu : AliasSupported u R)
    (B K : ℕ) (hB : R+K ≤ B) :
    Represents (extendAliasArray B (cachedInverseApply t E r B f K))
      (Neumann.inverseApprox (scaledFreeInverse t E (fun j => (r j : ℝ)) hr ht hE)
        calibrationMaterialPerturbation K u) := by
  induction K with
  | zero =>
    have hzero : Represents (0 : RationalAliasField) (0 : FiberSpace) := by
      intro ν j
      exact map_zero rationalComplexLinear
    have hz := represents_sample_extend hzero B (AliasSupported.zero B)
    simpa only [cachedInverseApply, Neumann.inverseApprox, Neumann.partialSeries,
      Finset.range_zero, Finset.sum_empty, mul_zero, zero_apply] using hz
  | succ K ih =>
    have hp := ih (by omega : R+K ≤ B)
    have hs := represents_sub (represents_freeApply t E r hr ht hE hf)
      (represents_freeApply t E r hr ht hE (represents_perturbation hp))
    have heq : scaledFreeInverse t E (fun j => (r j : ℝ)) hr ht hE u-
        scaledFreeInverse t E (fun j => (r j : ℝ)) hr ht hE
          (calibrationMaterialPerturbation
            (Neumann.inverseApprox (scaledFreeInverse t E (fun j => (r j : ℝ)) hr ht hE)
              calibrationMaterialPerturbation K u)) =
      Neumann.inverseApprox (scaledFreeInverse t E (fun j => (r j : ℝ)) hr ht hE)
        calibrationMaterialPerturbation (K+1) u := by
      rw [Neumann.inverseApprox_left_recurrence]
      rfl
    rw [heq] at hs
    exact represents_sample_extend hs B
      ((scaledInverseApprox_supported t E (fun j => (r j : ℝ)) hr ht hE hu (K+1)).mono hB)

#print axioms cachedInverseApply_sound

end Maxwell.Continuum.Calibration
