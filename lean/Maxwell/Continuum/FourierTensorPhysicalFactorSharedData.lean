import Maxwell.Continuum.FourierTensorPhysicalFactor
import Maxwell.Continuum.RationalDataflowBinaryValues
import Maxwell.Continuum.NatAssignExternalWord
import Maxwell.Continuum.NatAssignCleanup

/-! The computed physical normalization is copied into a rational register
and all square-root scratch words are cleared by fixed instructions. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.PhysicalFactorMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def allIds (S : Finset ℕ) : Finset ℕ := RationalDataflow.ids S∪ids
def workspace (S : Finset ℕ) : Finset ℕ := {0,1,2,3}∪allIds S
def Clean (s : BitRAMState) : Prop := ∀i∈RationalRoot.ids,Blank s i
def parameters (M P : ℕ) (v : ℕ→ℕ) : ℕ→ℕ := Function.update (Function.update v 350 M) 351 P
def initialJoined (M P : ℕ) (v : ℕ→Parts) : ℕ→ℕ := parameters M P (dataValues v)
def returnedJoined (M P : ℕ) (v : ℕ→Parts) (i : ℕ) : ℕ :=
  if i∈ids then outputValues M P i else dataValues v i
def factorParts (M P : ℕ) : Parts := ⟨Nat.sqrt (rootArgument M P),0,denominator M*2^P⟩
def privateTapes : List ℕ := [30,31,32,33,34,35,36,40,530,531,532,533,534,540,541,542,543,544,548]
def copyOutput (target : ℕ) : List NatAssign.Instruction :=
  [.copy 32 (positivePort target),.literal (negativePort target) 0,.copy 548 (denominatorPort target)]
def finishCall (target : ℕ) : List NatAssign.Instruction := copyOutput target++NatAssign.clearList privateTapes
def sharedCode (target : ℕ) : Code := .seq code (NatAssign.code (finishCall target))

theorem allIds_ge (S : Finset ℕ) (i : ℕ) (hi : i∈allIds S) : 4 ≤ i := by
  rcases Finset.mem_union.mp hi with hi|hi
  · exact RationalDataflow.ids_ge S i hi
  · exact ids_ge i hi

theorem ids_small (i : ℕ) (hi : i∈ids) : i<1000 := by
  simp only [ids,RationalRoot.ids,NaturalRoot.fullIds,NaturalRoot.ids,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
  omega

theorem privateTapes_mem (i : ℕ) : i∈privateTapes ↔ i∈RationalRoot.ids := by
  simp only [privateTapes,List.mem_cons,List.not_mem_nil,or_false,RationalRoot.ids,
    NaturalRoot.fullIds,NaturalRoot.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
  omega

theorem parameters_outside (S : Finset ℕ) (i : ℕ) (hi : i=350 ∨ i=351) : i∉RationalDataflow.ids S := by
  intro hm
  rcases Finset.mem_union.mp hm with hm|hm
  · obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hm
    have hp := positivePort_ge r
    have hn := negativePort_ge r
    have hd := denominatorPort_ge r
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hr
    omega
  · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hm
    omega

theorem initialJoined_small (M P : ℕ) (v : ℕ→Parts) (i : ℕ) (hi : i<1000) :
    initialJoined M P v i=initial M P i := by
  simp only [initialJoined,parameters,Function.update_apply,dataValues_small v hi,initial]
  split_ifs <;> omega

theorem initialJoined_outside (M P : ℕ) (v : ℕ→Parts) (i : ℕ) (hi : i∉ids) :
    initialJoined M P v i=dataValues v i := by
  have h350 : i≠350 := fun he => hi (he ▸ (by decide : 350∈ids))
  have h351 : i≠351 := fun he => hi (he ▸ (by decide : 351∈ids))
  simp only [initialJoined,parameters,Function.update_of_ne h350,Function.update_of_ne h351]

theorem initialJoined_bank (S : Finset ℕ) (M P : ℕ) (v : ℕ→Parts) (s : Store)
    (hr : Ready S v s) (hz : Clean s.val) (hm : Word s.val 350 M) (hp : Word s.val 351 P) :
    NatAssign.Bank (allIds S) (initialJoined M P v) s.val := by
  intro i hi
  by_cases h350 : i=350
  · subst i;simpa [initialJoined,parameters] using hm
  by_cases h351 : i=351
  · subst i;simpa [initialJoined,parameters] using hp
  rcases Finset.mem_union.mp hi with hi|hi
  · simpa only [initialJoined,parameters,Function.update_of_ne h350,Function.update_of_ne h351] using hr.1 i hi
  · have hroot : i∈RationalRoot.ids := (Finset.mem_union.mp hi).resolve_right (by simp [h350,h351])
    simpa only [initialJoined_small M P v i (ids_small i hi),initial,h350,h351,ite_false] using
      (RationalAccumulator.zero_word_iff_blank s.val i).mpr (hz i hroot)

theorem factorParts_value (M P : ℕ) (hM : 0<M) :
    (factorParts M P).value=Supercell.physicalFactorApprox M P := by
  simpa only [factorParts,Parts.value,Nat.cast_zero,sub_zero,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using factor_value M P hM

theorem factorParts_valid (M P : ℕ) (hM : 0<M) : (factorParts M P).Valid :=
  Nat.mul_pos (denominator_pos M hM) (by positivity)

theorem returned_output (M P : ℕ) (v : ℕ→Parts) :
    (⟨returnedJoined M P v 32,0,returnedJoined M P v 548⟩:Parts)=factorParts M P := by
  simp [returnedJoined,outputValues,show (32:ℕ)∈ids by decide,show (548:ℕ)∈ids by decide,
    show (32:ℕ)∈NaturalRoot.fullIds by decide,show (548:ℕ)∉NaturalRoot.fullIds by decide,
    NaturalRoot.doneValues,DyadicSqrt.bank,RationalRoot.preparedValues,factorParts]

theorem copyOutput_values (target : ℕ) (v : ℕ→ℕ) :
    NatAssign.values (copyOutput target) v=writeParts v target ⟨v 32,0,v 548⟩ := by
  have hp := positivePort_ge target
  have hn := negativePort_ge target
  simp (disch := omega) [copyOutput,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,writeParts]

theorem finishCall_values (M P : ℕ) (v : ℕ→Parts) (target : ℕ) :
    NatAssign.values (finishCall target) (returnedJoined M P v)=
      initialJoined M P (Function.update v target (factorParts M P)) := by
  rw [finishCall,values_append,copyOutput_values,returned_output]
  have hp := positivePort_ge target
  have hn := negativePort_ge target
  have hd := denominatorPort_ge target
  ext i
  simp only [NatAssign.clearList_values,privateTapes_mem,initialJoined,parameters]
  by_cases h350 : i=350
  · subst i
    simp (disch := omega) [writeParts,returnedJoined,outputValues,show (350:ℕ)∈ids by decide,
      show (350:ℕ)∉RationalRoot.ids by decide]
  by_cases h351 : i=351
  · subst i
    simp (disch := omega) [writeParts,returnedJoined,outputValues,show (351:ℕ)∈ids by decide,
      show (351:ℕ)∉RationalRoot.ids by decide]
  by_cases hi : i∈RationalRoot.ids
  · have hsmall := ids_small i (Finset.mem_union_left _ hi)
    simp only [hi,ite_true,Function.update_of_ne h350,Function.update_of_ne h351,dataValues_small _ hsmall]
  · have hnid : i∉ids := by simp [ids,hi,h350,h351]
    simp only [hi,ite_false,Function.update_of_ne h350,Function.update_of_ne h351]
    rw [←writeParts_dataValues]
    simp only [writeParts,Function.update_apply,returnedJoined]
    split_ifs <;> rfl

#print axioms factorParts_value
#print axioms finishCall_values
end Maxwell.Continuum.Profile.WaveMachine.Runtime.PhysicalFactorMachine
