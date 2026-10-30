import Maxwell.Continuum.CalibrationArrayAffine

/-! The cached matrix entries are the literal eighteen-neighbor stencil,
with executable cube coordinates. No dense linear-map evaluator is needed. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber
set_option maxHeartbeats 2000000

def arrayAliasAt (R : ℕ) (i : Fin (aliasArraySize R)) : Alias :=
  arrayAlias R ((aliasArrayEquiv R).symm i).1

def arrayPolarizationAt (R : ℕ) (i : Fin (aliasArraySize R)) : Fin 3 :=
  ((aliasArrayEquiv R).symm i).2

def pointBasis (μ : Alias) (j : Fin 3) : RationalRealField :=
  fun ν k => if ν=μ ∧ k=j then 1 else 0

theorem arrayExtendLinear_single (R : ℕ) (j : Fin (aliasArraySize R)) :
    arrayExtendLinear R (Pi.single j 1) = pointBasis (arrayAliasAt R j) (arrayPolarizationAt R j) := by
  funext ν k
  have hj : aliasInCube R (arrayAliasAt R j) := arrayAlias_mem R _
  by_cases hν : aliasInCube R ν
  · have hi : arrayAliasIndex R ν hν = ((aliasArrayEquiv R).symm j).1 ↔ ν=arrayAliasAt R j := by
      constructor
      · intro h
        simpa only [arrayAlias_index,arrayAliasAt] using congrArg (arrayAlias R) h
      · intro h
        subst ν
        exact arrayIndex_alias R _
    have hpair : aliasArrayEquiv R (arrayAliasIndex R ν hν,k) = j ↔
        ν=arrayAliasAt R j ∧ k=arrayPolarizationAt R j := by
      rw [← Equiv.eq_symm_apply,Prod.mk.injEq,hi]
      rfl
    simp only [arrayExtendLinear,LinearMap.coe_mk,AddHom.coe_mk,hν,dite_true,
      Pi.single_apply,pointBasis,hpair]
  · have hn : ν ≠ arrayAliasAt R j := fun h => hν (h ▸ hj)
    simp only [arrayExtendLinear,LinearMap.coe_mk,AddHom.coe_mk,hν,dite_false,pointBasis,hn,
      false_and,ite_false]

def stencilEntry (t E : ℚ) (r : Fin 3 → ℚ) (ν : Alias) (i : Fin 3) (μ : Alias) (j : Fin 3) : ℚ :=
  -(∑ k : Fin 3, rationalFreeInverseMatrix t E r ν i k *
    (-rationalAmplitude * if rationalCentralCheck ν then 0 else
      ∑ d : Fin 3, rationalWeight d *
        ((if rationalCentralCheck (ν+unitAlias d) then 0 else pointBasis μ j (ν+unitAlias d) k)+
         (if rationalCentralCheck (ν-unitAlias d) then 0 else pointBasis μ j (ν-unitAlias d) k))))

theorem cachedTransitionMatrix_entry (t E : ℚ) (r : Fin 3 → ℚ) (R : ℕ)
    (i j : Fin (aliasArraySize R)) :
    cachedTransitionMatrix t E r R i j =
      stencilEntry t E r (arrayAliasAt R i) (arrayPolarizationAt R i)
        (arrayAliasAt R j) (arrayPolarizationAt R j) := by
  rw [cachedTransitionMatrix,LinearMap.toMatrix'_apply]
  simp only [cachedTransitionLinear,LinearMap.neg_apply,LinearMap.comp_apply,Pi.neg_apply]
  rw [arrayExtendLinear_single]
  rfl

theorem cachedForcing_entry (t E : ℚ) (r : Fin 3 → ℚ) (R : ℕ)
    (f : RationalRealField) (i : Fin (aliasArraySize R)) :
    cachedForcing t E r R f i =
      ∑ j : Fin 3, rationalFreeInverseMatrix t E r (arrayAliasAt R i) (arrayPolarizationAt R i) j *
        f (arrayAliasAt R i) j := rfl

#print axioms cachedTransitionMatrix_entry
#print axioms cachedForcing_entry

end Maxwell.Continuum.Calibration
