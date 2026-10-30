import Maxwell.Continuum.CalibrationCachedNeumann
import Maxwell.Continuum.CalibrationRationalSupport

/-! The materialized cache equals the executable rational recurrence
entry by entry. The alias-radius condition is discharged by literal
finite propagation, for real or complex input coefficients. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

omit [Module ℚ V] in
theorem extend_sample_supported {f : Alias → Fin 3 → V} {B : ℕ}
    (hf : RationalSupported f B) : extendAliasArray B (sampleAliasArray B f) = f := by
  funext ν j
  rw [extend_sample_alias]
  by_cases hν : aliasInCube B ν
  · simp only [hν,↓reduceIte]
  · have hout : ∃ k, (B : ℤ) < |ν k| := by
      simpa only [aliasInCube,not_forall,not_le] using hν
    rw [hf ν hout j]
    simp only [hν,↓reduceIte]

theorem cachedInverseApply_exact (t E : ℚ) (r : Fin 3 → ℚ)
    {f : Alias → Fin 3 → V} {R : ℕ} (hf : RationalSupported f R) (B K : ℕ)
    (hB : R+K ≤ B) :
    extendAliasArray B (cachedInverseApply t E r B f K) = rationalInverseApply t E r f K := by
  induction K with
  | zero => exact extend_sample_supported (RationalSupported.zero B)
  | succ K ih =>
    change extendAliasArray B (sampleAliasArray B (rationalFreeApply t E r f-
      rationalFreeApply t E r (rationalPerturbation
        (extendAliasArray B (cachedInverseApply t E r B f K))))) = _
    rw [ih (by omega)]
    exact extend_sample_supported ((hf.inverseApply t E r (K+1)).mono hB)

#print axioms cachedInverseApply_exact

end Maxwell.Continuum.Calibration
