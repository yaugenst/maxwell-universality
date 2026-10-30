import Maxwell.Continuum.CalibrationCachedNeumann
import Maxwell.Continuum.CalibrationSharedDenominator

/-! The actual cached stencil is an affine finite rational recurrence.
Its coefficient matrix is extracted from that literal linear map. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber
open scoped Matrix

abbrev RationalRealField := Alias → Fin 3 → ℚ

def rationalNoncentralLinear : RationalRealField →ₗ[ℚ] RationalRealField where
  toFun := rationalNoncentral
  map_add' f g := by
    funext ν j
    by_cases hν : rationalCentralCheck ν = true <;> simp [rationalNoncentral,hν]
  map_smul' c f := by
    funext ν j
    by_cases hν : rationalCentralCheck ν = true <;> simp [rationalNoncentral,hν]

def rationalPotentialLinear : RationalRealField →ₗ[ℚ] RationalRealField where
  toFun := rationalPotential
  map_add' f g := by
    funext ν j
    simp only [rationalPotential,Pi.add_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    funext ν j
    simp only [rationalPotential,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,RingHom.id_apply]
    simp_rw [← mul_assoc, mul_comm _ c, mul_assoc, ← Finset.mul_sum]

def rationalPerturbationLinear : RationalRealField →ₗ[ℚ] RationalRealField :=
  (-rationalAmplitude) • rationalNoncentralLinear.comp (rationalPotentialLinear.comp rationalNoncentralLinear)

theorem rationalPerturbationLinear_apply (f : RationalRealField) :
    rationalPerturbationLinear f = rationalPerturbation f := rfl

def rationalFreeLinear (t E : ℚ) (r : Fin 3 → ℚ) : RationalRealField →ₗ[ℚ] RationalRealField where
  toFun := rationalFreeApply t E r
  map_add' f g := by
    funext ν j
    simp only [rationalFreeApply,Pi.add_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
  map_smul' c f := by
    funext ν j
    simp only [rationalFreeApply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp_rw [← mul_assoc, mul_comm _ c, mul_assoc, ← Finset.mul_sum]

def arraySampleLinear (B : ℕ) : RationalRealField →ₗ[ℚ] (Fin (aliasArraySize B) → ℚ) where
  toFun f i := f (arrayAlias B ((aliasArrayEquiv B).symm i).1) ((aliasArrayEquiv B).symm i).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def arrayExtendLinear (B : ℕ) : (Fin (aliasArraySize B) → ℚ) →ₗ[ℚ] RationalRealField where
  toFun x ν j := if hν : aliasInCube B ν then x (aliasArrayEquiv B (arrayAliasIndex B ν hν,j)) else 0
  map_add' x y := by
    funext ν j
    by_cases hν : aliasInCube B ν <;> simp [hν]
  map_smul' c x := by
    funext ν j
    by_cases hν : aliasInCube B ν <;> simp [hν]

theorem arrayExtendLinear_vector (B : ℕ) (x : Fin (aliasArraySize B) → ℚ) :
    arrayExtendLinear B x = extendAliasArray B (Vector.ofFn x) := by
  funext ν j
  change (if hν : aliasInCube B ν then x _ else 0) = _
  unfold extendAliasArray
  split_ifs
  · exact (vector_get_ofFn _ _).symm
  · rfl

def cachedTransitionLinear (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ) :
    (Fin (aliasArraySize B) → ℚ) →ₗ[ℚ] (Fin (aliasArraySize B) → ℚ) :=
  -(arraySampleLinear B).comp ((rationalFreeLinear t E r).comp
    (rationalPerturbationLinear.comp (arrayExtendLinear B)))

def cachedTransitionMatrix (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ) :
    Matrix (Fin (aliasArraySize B)) (Fin (aliasArraySize B)) ℚ :=
  LinearMap.toMatrix' (cachedTransitionLinear t E r B)

def cachedForcing (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ) (f : RationalRealField) :
    Fin (aliasArraySize B) → ℚ := arraySampleLinear B (rationalFreeApply t E r f)

theorem cachedTransitionMatrix_apply (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ)
    (x : Fin (aliasArraySize B) → ℚ) :
    (cachedTransitionMatrix t E r B) *ᵥ x = cachedTransitionLinear t E r B x := by
  exact LinearMap.toMatrix'_mulVec _ _

end Maxwell.Continuum.Calibration
