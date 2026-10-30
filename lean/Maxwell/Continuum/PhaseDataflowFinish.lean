import Maxwell.Continuum.PhaseDataflowStages

/-! Exact output transfer and clearing for a shared-bank phase call. -/
namespace Maxwell.Continuum.RationalDataflow.Phase
open Maxwell.Cost Maxwell.Cost.Structured RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem copyOutput_values (target : ℕ) (v : ℕ→ℕ) :
    NatAssign.values (copyOutput target) v=writeParts v target ⟨v 602,v 603,v 604⟩ := by
  have hp := positivePort_ge target
  have hn := negativePort_ge target
  simp (disch := omega) [copyOutput,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,writeParts]

theorem returned_output (base : ℕ→Sign) (Q N : ℕ) (v : ℕ→Parts) (source : ℕ) :
    (⟨returned base Q N v source 602,returned base Q N v source 603,
      returned base Q N v source 604⟩ : Parts)=result base Q N (v source) := by
  simp only [returned,result,show 602∈PhaseMachine.allIds by decide,
    show 603∈PhaseMachine.allIds by decide,show 604∈PhaseMachine.allIds by decide,ite_true]

theorem finishCall_values (base : ℕ→Sign) (Q N : ℕ) (v : ℕ→Parts) (target source : ℕ) :
    NatAssign.values (finishCall target) (returned base Q N v source)=
      dataValues (Function.update v target (result base Q N (v source))) := by
  rw [finishCall,values_append,copyOutput_values,returned_output,←writeParts_dataValues]
  have hp := positivePort_ge target
  have hn := negativePort_ge target
  have hd := denominatorPort_ge target
  ext i
  simp only [NatAssign.clearList_values,privateTapes_mem]
  by_cases hi : i∈PhaseMachine.allIds
  · have hsmall := PhaseMachine.allIds_small i hi
    simp (disch := omega) [hi,writeParts,dataValues_small v hsmall]
  · simp only [hi,ite_false,writeParts,Function.update_apply,returned]

theorem finishCall_literalWidth (target : ℕ) :
    ∀a∈finishCall target,a.literalWidth=0 := by
  intro a ha
  rcases List.mem_append.mp ha with ho|hz
  · simp only [copyOutput,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl <;> rfl
  · exact NatAssign.clearList_literalWidth privateTapes a hz

theorem clean_of_bank (S : Finset ℕ) (v : ℕ→Parts) (s : BitRAMState)
    (h : NatAssign.Bank (allIds S) (dataValues v) s) : Clean s := by
  intro i hi
  have hw := h i (Finset.mem_union_right _ hi)
  rw [dataValues_small v (PhaseMachine.allIds_small i hi)] at hw
  exact (RationalAccumulator.zero_word_iff_blank _ _).mp hw

#print axioms finishCall_values
#print axioms clean_of_bank
end Maxwell.Continuum.RationalDataflow.Phase
