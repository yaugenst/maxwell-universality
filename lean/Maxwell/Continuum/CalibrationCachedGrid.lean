import Maxwell.Continuum.CalibrationCachedFull
import Maxwell.Continuum.CalibrationCutoffGrid

/-! The executable cutoff inverse returns an actual finite array.
The two full-inverse caches are formed before the final sample map. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

def cachedGridVector {V : Type*} [AddCommGroup V] [Module ℚ V]
    (z σ : ℚ) (r : Fin 3 → ℚ) (R K P : ℕ) (f : Alias → Fin 3 → V) :
    Vector V (aliasArraySize (R+K+2)) :=
  if activeGrid r then
    let a := cachedFullVector (piCenter K) (z+σ+7) r R K f
    sampleAliasArray (R+K+2) ((gridCutoffApprox r P).center • extendAliasArray (R+K+2) a)
  else sampleAliasArray (R+K+2) 0

theorem cachedGridVector_eq {V : Type*} [AddCommGroup V] [Module ℚ V]
    (z σ : ℚ) (r : Fin 3 → ℚ) (R K P : ℕ) {f : Alias → Fin 3 → V}
    (hf : RationalSupported f R) :
    extendAliasArray (R+K+2) (cachedGridVector z σ r R K P f) = rationalGridApply z σ r K P f := by
  by_cases hr : activeGrid r
  · simp only [cachedGridVector,rationalGridApply,hr,↓reduceIte]
    rw [cachedFullVector_eq _ _ _ _ _ hf]
    exact extend_sample_supported ((hf.fullApply _ _ _ _).smul _)
  · simp only [cachedGridVector,rationalGridApply,hr,↓reduceIte]
    exact extend_sample_supported (RationalSupported.zero _)

#print axioms cachedGridVector_eq

end Maxwell.Continuum.Calibration
