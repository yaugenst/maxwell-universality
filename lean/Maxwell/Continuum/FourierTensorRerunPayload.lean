import Maxwell.Continuum.FourierTensorOutputPayload

/-! Deterministic mode reruns may use different allocated arrays. Equality
of their actual Fourier data gives the same declared component payload. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost RationalDataflow PartArray Calibration Calibration.FiniteAlgorithm
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] FiniteAlgorithm.mode FiniteAlgorithm.size MasterConstants.exponent

theorem componentPayload_eq_of_data (M A L R P Q N : ℕ)
    (a b : Table (2*aliasArraySize R)) (j : Fin 3)
    (hab : GlobalPower.tableData R a=GlobalPower.tableData R b) :
    componentPayload M A L R P Q N a j=componentPayload M A L R P Q N b j := by
  have h : amplitude M A P R a j=amplitude M A P R b j := by
    funext row
    simp only [amplitude,hab]
  simp only [componentPayload,h]

theorem outputComponentPayload_eq_of_data (L r N : ℕ) (z : ℚ)
    (a b : Table (2*aliasArraySize (FiniteAlgorithm.mode L r (N+2) z).radius)) (j : Fin 3)
    (hab : GlobalPower.tableData (FiniteAlgorithm.mode L r (N+2) z).radius a=
      GlobalPower.tableData (FiniteAlgorithm.mode L r (N+2) z).radius b) :
    outputComponentPayload L r N z a j=outputComponentPayload L r N z b j :=
  componentPayload_eq_of_data _ _ _ _ _ _ _ a b j hab

theorem outputTemplateBits_reruns (L r N : ℕ) (z : ℚ)
    (a : Fin 3→Table (2*aliasArraySize (FiniteAlgorithm.mode L r (N+2) z).radius))
    (ha : ∀j,GlobalPower.tableData (FiniteAlgorithm.mode L r (N+2) z).radius (a j)=
      FiniteAlgorithm.mode L r (N+2) z) :
    outputTemplateBits L r N z=outputTemplateHeader L r N z++
      outputComponentPayload L r N z (a 0) 0++outputComponentPayload L r N z (a 1) 1++
      outputComponentPayload L r N z (a 2) 2 := by
  have h := outputTemplateBits_components L r N z (a 0) (ha 0)
  have h1 := outputComponentPayload_eq_of_data L r N z (a 0) (a 1) 1 ((ha 0).trans (ha 1).symm)
  have h2 := outputComponentPayload_eq_of_data L r N z (a 0) (a 2) 2 ((ha 0).trans (ha 2).symm)
  simpa only [h1,h2] using h

#print axioms outputTemplateBits_reruns
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
