import Maxwell.Continuum.CalibrationGlobalPower

/-! Exact finite-data output of the fixed-matrix power computation. Equalities
here identify the literal arrays used by subsequent normalization and scalar
calibration; they do not merely identify their represented Hilbert vectors. -/

namespace Maxwell.Continuum.Calibration
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

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

namespace GlobalPower

def rawModeData (L r N : ℕ) (z : ℚ) : FourierData :=
  ⟨modeRadius L r N,unpack (modeRadius L r N)
    (PowerMachine.rationalPower (modeMatrix L r N z)
      (sample (modeRadius L r N) (FiniteAlgorithm.seed L r N).field)
      (FiniteAlgorithm.iterations N))⟩

theorem rawModeData_eq (L r N : ℕ) (z : ℚ) :
    rawModeData L r N z=FiniteAlgorithm.rawMode L r N z := by
  apply FourierData.eq_of_radius_field
  · change modeRadius L r N=(FiniteAlgorithm.rawMode L r N z).radius
    rw [FiniteAlgorithm.rawMode,FourierData.iterate_radius]
    rfl
  · exact rawMode_fixed_matrix L r N z

theorem normalizedMode_eq (L r N : ℕ) (z : ℚ) :
    FourierData.normalizeData (FiniteAlgorithm.precision L r N) (rawModeData L r N z)=
      FiniteAlgorithm.mode L r N z := by
  rw [rawModeData_eq]
  rfl

theorem rawModeData_value (L r N : ℕ) (z : ℚ) :
    (rawModeData L r N z).value=(FiniteAlgorithm.rawMode L r N z).value := by
  rw [rawModeData_eq]

#print axioms rawModeData_eq
#print axioms normalizedMode_eq

end GlobalPower
end Maxwell.Continuum.Calibration
