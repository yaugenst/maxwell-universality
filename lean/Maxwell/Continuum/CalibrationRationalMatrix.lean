import Maxwell.Continuum.CalibrationRationalReal
import Maxwell.Continuum.CalibrationCentralIndex

/-! An executable rational 24-by-24 matrix for the actual finite Schur
approximation, with an orthonormal coordinate identification. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

def rationalBasisField (i : Fin 24) : Alias → Fin 3 → ℚ := fun ν j =>
  if ν = rationalCubeAlias (centralIndexFin.symm i).1 ∧ j = (centralIndexFin.symm i).2 then 1 else 0

theorem rationalBasisField_sound (i : Fin 24) :
    RealRepresents (rationalBasisField i)
      (centralFinUnitary (EuclideanSpace.single i (1 : ℂ))).val := by
  intro ν j
  by_cases hν : IsCentralAlias ν
  · obtain ⟨s,hs⟩ := CornerBridge.parityAliasEquiv.surjective ⟨ν,hν⟩
    have ha : rationalCubeAlias s = ν := congrArg Subtype.val hs
    rw [← ha, centralFinUnitary_apply]
    have hi : centralIndexFin (s,j) = i ↔ s = (centralIndexFin.symm i).1 ∧ j = (centralIndexFin.symm i).2 := by
      rw [← Equiv.eq_symm_apply, Prod.mk.injEq]
    simp only [rationalBasisField, rationalCubeAlias_injective.eq_iff,
      PiLp.single_apply, hi]
    split_ifs <;> norm_num
  · have hn : ν ≠ rationalCubeAlias (centralIndexFin.symm i).1 := by
      intro h
      apply hν
      rw [h, rationalCubeAlias_eq]
      exact CornerBridge.alias_central _
    rw [centralSpace_noncentral _ ν hν]
    simp only [rationalBasisField, hn, false_and, ↓reduceIte, Rat.cast_zero]
    rfl

def rationalSchurMatrix (t E : ℚ) (r : Fin 3 → ℚ) (K : ℕ) : Matrix (Fin 24) (Fin 24) ℚ :=
  fun i j => rationalSchurApply t E r K (rationalBasisField j)
    (rationalCubeAlias (centralIndexFin.symm i).1) (centralIndexFin.symm i).2

noncomputable def centralFinOperator (A : centralSpace →L[ℂ] centralSpace) :
    EuclideanSpace ℂ (Fin 24) →L[ℂ] EuclideanSpace ℂ (Fin 24) :=
  centralFinUnitary.symm.toLinearIsometry.toContinuousLinearMap.comp
    (A.comp centralFinUnitary.toLinearIsometry.toContinuousLinearMap)

theorem rationalSchurMatrix_column (t E : ℚ) (r : Fin 3 → ℚ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (ht : (3 : ℝ) ≤ t ∧ (t : ℝ) ≤ 4)
    (hE : (7 : ℝ) ≤ E ∧ (E : ℝ) ≤ 8) (K : ℕ) (i j : Fin 24) :
    (rationalSchurMatrix t E r K i j : ℂ) =
      centralFinOperator (scaledFiniteSchurApprox t E (fun j => (r j : ℝ)) hr ht hE K)
        (EuclideanSpace.single j 1) i := by
  have h := realRepresents_schurApply t E r hr ht hE (rationalBasisField_sound j) K
  change _ = centralFinUnitary.symm
    (scaledFiniteSchurApprox t E (fun j => (r j : ℝ)) hr ht hE K
      (centralFinUnitary (EuclideanSpace.single j 1))) i
  rw [centralFinUnitary_symm_apply]
  exact h _ _

noncomputable def centralMatrixCLM (M : Matrix (Fin 24) (Fin 24) ℂ) :
    EuclideanSpace ℂ (Fin 24) →L[ℂ] EuclideanSpace ℂ (Fin 24) :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

theorem rationalSchurMatrix_sound (t E : ℚ) (r : Fin 3 → ℚ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (ht : (3 : ℝ) ≤ t ∧ (t : ℝ) ≤ 4)
    (hE : (7 : ℝ) ≤ E ∧ (E : ℝ) ≤ 8) (K : ℕ) :
    centralMatrixCLM ((rationalSchurMatrix t E r K).map (Rat.castHom ℂ)) =
      centralFinOperator (scaledFiniteSchurApprox t E (fun j => (r j : ℝ)) hr ht hE K) := by
  apply ContinuousLinearMap.coe_injective
  change Matrix.toEuclideanLin _ = _
  apply Matrix.toEuclideanLin.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change _ = (Matrix.toLpLin 2 2).symm _
  rw [Matrix.toLpLin_eq_toLin, Matrix.toLin_symm]
  ext i j
  rw [LinearMap.toMatrix_apply, PiLp.basisFun_repr, PiLp.basisFun_apply]
  exact rationalSchurMatrix_column t E r hr ht hE K i j

#print axioms rationalSchurMatrix_sound

end Maxwell.Continuum.Calibration
