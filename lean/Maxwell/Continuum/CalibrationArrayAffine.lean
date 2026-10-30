import Maxwell.Continuum.CalibrationArrayLinear

/-! Exact affine recurrence for the actual materialized rational alias
arrays, followed by one computed common denominator for its coefficients. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber
open scoped Matrix

def rationalAffineIteration {n : ℕ} (T : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) : ℕ → Fin n → ℚ
  | 0 => 0
  | K+1 => b+T *ᵥ rationalAffineIteration T b K

theorem arrayExtendLinear_get (B : ℕ) (a : Vector ℚ (aliasArraySize B)) :
    arrayExtendLinear B (fun i => a.get i) = extendAliasArray B a := rfl

theorem sampleAliasArray_get (B : ℕ) (f : RationalRealField) (i : Fin (aliasArraySize B)) :
    (sampleAliasArray B f).get i = arraySampleLinear B f i := vector_get_ofFn _ _

theorem cachedInverseApply_affine_step (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ)
    (f : RationalRealField) (K : ℕ) (i : Fin (aliasArraySize B)) :
    (cachedInverseApply t E r B f (K+1)).get i = cachedForcing t E r B f i+
      (cachedTransitionMatrix t E r B *ᵥ (fun j => (cachedInverseApply t E r B f K).get j)) i := by
  rw [cachedTransitionMatrix_apply]
  change (sampleAliasArray B (rationalFreeApply t E r f-rationalFreeApply t E r
    (rationalPerturbation (extendAliasArray B (cachedInverseApply t E r B f K))))).get i = _
  rw [sampleAliasArray_get]
  simp only [cachedTransitionLinear,LinearMap.neg_apply,LinearMap.comp_apply,Pi.neg_apply]
  change _ = cachedForcing t E r B f i+ -
    arraySampleLinear B (rationalFreeApply t E r (rationalPerturbation
      (arrayExtendLinear B (fun j => (cachedInverseApply t E r B f K).get j)))) i
  rw [arrayExtendLinear_get]
  convert! congrFun ((arraySampleLinear B).map_sub (rationalFreeApply t E r f)
    (rationalFreeApply t E r (rationalPerturbation
      (extendAliasArray B (cachedInverseApply t E r B f K))))) i using 1
  simp only [Pi.sub_apply,cachedForcing,sub_eq_add_neg]

theorem cachedInverseApply_affine (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ)
    (f : RationalRealField) (K : ℕ) :
    (fun i => (cachedInverseApply t E r B f K).get i) =
      rationalAffineIteration (cachedTransitionMatrix t E r B) (cachedForcing t E r B f) K := by
  induction K with
  | zero =>
    funext i
    exact sampleAliasArray_get B 0 i
  | succ K ih =>
    funext i
    rw [cachedInverseApply_affine_step,ih]
    rfl

def cachedCoefficientTable (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ) (f : RationalRealField) :
    (Fin (aliasArraySize B) ⊕ (Fin (aliasArraySize B) × Fin (aliasArraySize B))) → ℚ :=
  Sum.elim (cachedForcing t E r B f) (fun ij => cachedTransitionMatrix t E r B ij.1 ij.2)

def cachedDenominator (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ) (f : RationalRealField) : ℕ :=
  commonDenominator (cachedCoefficientTable t E r B f)

def cachedIntegerSource (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ) (f : RationalRealField) :
    Fin (aliasArraySize B) → ℤ := fun i =>
  commonNumerator (cachedCoefficientTable t E r B f) (.inl i)

def cachedIntegerTransition (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ) (f : RationalRealField) :
    Fin (aliasArraySize B) → Fin (aliasArraySize B) → ℤ := fun i j =>
  commonNumerator (cachedCoefficientTable t E r B f) (.inr (i,j))

theorem cachedDenominator_pos (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ) (f : RationalRealField) :
    0 < cachedDenominator t E r B f := commonDenominator_pos _

theorem cachedIntegerSource_sound (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ) (f : RationalRealField)
    (i : Fin (aliasArraySize B)) :
    (cachedIntegerSource t E r B f i : ℚ)/cachedDenominator t E r B f = cachedForcing t E r B f i :=
  commonNumerator_sound (cachedCoefficientTable t E r B f) (Sum.inl i)

theorem cachedIntegerTransition_sound (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ) (f : RationalRealField)
    (i j : Fin (aliasArraySize B)) :
    (cachedIntegerTransition t E r B f i j : ℚ)/cachedDenominator t E r B f =
      cachedTransitionMatrix t E r B i j :=
  commonNumerator_sound (cachedCoefficientTable t E r B f) (Sum.inr (i,j))

theorem cachedInteger_iteration (t E : ℚ) (r : Fin 3 → ℚ) (B : ℕ) (f : RationalRealField) (K : ℕ)
    (i : Fin (aliasArraySize B)) :
    (sharedNumerator (cachedDenominator t E r B f) (cachedIntegerTransition t E r B f)
      (cachedIntegerSource t E r B f) K i : ℚ)/(cachedDenominator t E r B f : ℚ)^K =
        (cachedInverseApply t E r B f K).get i := by
  rw [sharedNumerator_sound _ (cachedDenominator_pos t E r B f)]
  have ha := congrFun (cachedInverseApply_affine t E r B f K) i
  rw [ha]
  clear ha
  induction K generalizing i with
  | zero => rfl
  | succ K ih =>
    simp only [sharedRationalIteration,rationalAffineIteration,Pi.add_apply,Matrix.mulVec, dotProduct]
    rw [cachedIntegerSource_sound]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [cachedIntegerTransition_sound,ih]

#print axioms cachedInteger_iteration

end Maxwell.Continuum.Calibration
