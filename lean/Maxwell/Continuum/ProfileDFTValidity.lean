import Maxwell.Continuum.ProfileDFTStepData

/-! Positive raw denominators are preserved throughout actual DFT sampling. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor
set_option maxHeartbeats 2500000

theorem angularValues_good (S : Finset ℕ) (hS : ({0,1,2,3,4}:Finset ℕ)⊆S)
    (P : ℕ) (v : ℕ→Parts) (hv : Good S v) : Good S (angularValues P v) := by
  have hx := hv 0 (hS (by decide))
  have hp : Good S (angularAfterPhase P v) := hv.update 1 (Phase.result_valid _ _ _ _ hx)
  have hm : Good S (angularAfterMiddle P v) := evaluate_good S angularMiddle (angularMiddle_valid S hS)
    (angularAfterPhase P v) hp (by simp [AdmissibleTrace,angularMiddle,Instruction.Admissible])
  exact hm.update 4 (angularParts_valid _ _ hx)

theorem dftStepValues_good (S : Finset ℕ) (hS : Finset.range 10⊆S)
    (D P : ℕ) (v : ℕ→Parts) (hv : Good S v) : Good S (dftStepValues D P v) := by
  have hsmall : ({0,1,2,3,4}:Finset ℕ)⊆S := Finset.Subset.trans (by decide) hS
  have ha := angularValues_good S hsmall P v hv
  have hb : Good S (dftAfterPreparation P v) := evaluate_good S dftPreparation
    (dftPreparation_valid S hS) (angularValues P v) ha (by
      simp [AdmissibleTrace,dftPreparation,Instruction.Admissible])
  have hc : Good S (dftAfterPhase D P v) := hb.update 7
    (Phase.result_valid _ _ _ _ (hb 6 (hS (by decide))))
  exact evaluate_good S dftFinish (dftFinish_valid S hS) (dftAfterPhase D P v) hc (by
    simp [AdmissibleTrace,dftFinish,Instruction.Admissible])

#print axioms dftStepValues_good
end Maxwell.Continuum.Profile.Runtime
