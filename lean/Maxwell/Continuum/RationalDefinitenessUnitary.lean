import Maxwell.Continuum.RationalDefinitenessOperator

/-! Transport of literal rational sign tests through orthonormal coordinates. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def unitaryPush (U : E ≃ₗᵢ[ℂ] H) (A : E →L[ℂ] E) : H →L[ℂ] H :=
  U.toLinearIsometry.toContinuousLinearMap.comp (A.comp U.symm.toLinearIsometry.toContinuousLinearMap)

theorem unitaryPush_apply (U : E ≃ₗᵢ[ℂ] H) (A : E →L[ℂ] E) (x : H) :
    unitaryPush U A x=U (A (U.symm x)) := rfl

theorem unitaryPush_norm (U : E ≃ₗᵢ[ℂ] H) (A : E →L[ℂ] E) : ‖unitaryPush U A‖=‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [unitaryPush_apply,U.norm_map]
    simpa only [U.symm.norm_map] using A.le_opNorm (U.symm x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (unitaryPush U A).le_opNorm (U x)
    simpa only [unitaryPush_apply,U.symm_apply_apply,U.norm_map] using h

theorem unitaryPush_sub (U : E ≃ₗᵢ[ℂ] H) (A B : E →L[ℂ] E) :
    unitaryPush U (A-B)=unitaryPush U A-unitaryPush U B := by
  ext x
  simp only [unitaryPush_apply,sub_apply,map_sub]

theorem unitaryPush_inverse (U : E ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H) :
    unitaryPush U (unitaryPush U.symm A)=A := by
  ext x
  simp only [unitaryPush_apply,LinearIsometryEquiv.symm_symm,U.apply_symm_apply]

theorem unitaryPush_error (U : E ≃ₗᵢ[ℂ] H) (A : E →L[ℂ] E) (B : H →L[ℂ] H) :
    ‖unitaryPush U A-B‖=‖A-unitaryPush U.symm B‖ := by
  rw [← unitaryPush_norm U (A-unitaryPush U.symm B),unitaryPush_sub,unitaryPush_inverse]

theorem unitaryPush_inner (U : E ≃ₗᵢ[ℂ] H) (A : E →L[ℂ] E) (x : E) :
    inner ℂ (U x) (unitaryPush U A (U x))=inner ℂ x (A x) := by
  rw [unitaryPush_apply,U.symm_apply_apply,U.inner_map_map]

theorem negativeTest_unitary {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] H)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : ∀ i j, A i j=A j i) (h : negativeTest A=true) :
    ∀ u : H, u≠0 → (inner ℂ u (unitaryPush U (rationalOperator A) u)).re<0 := by
  intro u hu
  have hz : U.symm u≠0 := by
    intro he
    apply hu
    have h' := congrArg U he
    simpa only [U.apply_symm_apply,map_zero] using h'
  have hsign := (negativeTest_operator A hA).mp h (U.symm u) hz
  simpa only [← unitaryPush_inner U (rationalOperator A) (U.symm u),U.apply_symm_apply] using hsign

theorem negativeTest_unitary_false {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] H)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : ∀ i j, A i j=A j i) (h : negativeTest A=false) :
    ∃ u : H, u≠0 ∧ 0≤(inner ℂ u (unitaryPush U (rationalOperator A) u)).re := by
  obtain ⟨z,hz,hs⟩ := negativeTest_operator_false A hA h
  refine ⟨U z,?_,?_⟩
  · intro he
    apply hz
    exact U.injective (he.trans (map_zero U).symm)
  · rwa [unitaryPush_inner]

#print axioms negativeTest_unitary
#print axioms negativeTest_unitary_false
#print axioms unitaryPush_error

end Maxwell.Continuum.Calibration
