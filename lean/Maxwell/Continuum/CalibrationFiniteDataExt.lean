import Maxwell.Continuum.CalibrationFiniteData

/-! Extensionality of explicit finite Fourier data, independent of a
particular power iteration or normalization algorithm. -/
namespace Maxwell.Continuum.Calibration

theorem sample_extend_array {V : Type*} [Zero V] (R : ℕ)
    (a : Vector V (aliasArraySize R)) :
    sampleAliasArray R (extendAliasArray R a)=a := by
  apply Vector.ext
  intro i hi
  change (sampleAliasArray R (extendAliasArray R a)).get ⟨i,hi⟩=a.get ⟨i,hi⟩
  rw [sampleAliasArray,vector_get_ofFn,extendAliasArray,
    dite_eq_left (arrayAlias_mem R ((aliasArrayEquiv R).symm ⟨i,hi⟩).1)]
  simp only [arrayIndex_alias,Prod.mk.eta,Equiv.apply_symm_apply]

theorem FourierData.eq_of_radius_field {v w : FourierData}
    (hr : v.radius=w.radius) (hf : v.field=w.field) : v=w := by
  cases v with
  | mk R a =>
    cases w with
    | mk S b =>
      change R=S at hr
      subst S
      have hc := congrArg (sampleAliasArray R) hf
      change sampleAliasArray R (extendAliasArray R a)=sampleAliasArray R (extendAliasArray R b) at hc
      rw [sample_extend_array,sample_extend_array] at hc
      exact congrArg (FourierData.mk R) hc

#print axioms FourierData.eq_of_radius_field
end Maxwell.Continuum.Calibration
