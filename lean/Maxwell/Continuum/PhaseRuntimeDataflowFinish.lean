import Maxwell.Continuum.PhaseRuntimeDataflowStages

/-! The runtime phase call copies exact rational output words and clears
all temporary words while preserving its two stored numeric parameters. -/
namespace Maxwell.Continuum.RationalDataflow.Phase.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem finishCall_values (base : RationalTaylor.Runtime.Cycle) (Q N : ℕ)
    (v : ℕ→Parts) (target source : ℕ) :
    NatAssign.values (finishCall target) (returned base Q N v source)=
      initialValues Q N (Function.update v target (Phase.result (RationalTaylor.Runtime.cycleSigns base) Q N (v source))) := by
  rw [finishCall,values_append,Phase.copyOutput_values,returned_output]
  have hp := positivePort_ge target
  have hn := negativePort_ge target
  have hd := denominatorPort_ge target
  ext i
  simp only [NatAssign.clearList_values,privateTapes_mem,initialValues,parameters]
  by_cases h652 : i=652
  · subst i
    simp (disch := omega) [writeParts,(returned_parameters base Q N v source).1]
  by_cases h653 : i=653
  · subst i
    simp (disch := omega) [writeParts,(returned_parameters base Q N v source).2]
  by_cases hi : i∈PhaseMachine.Runtime.ids
  · have hsmall := ids_small i hi
    simp (disch := omega) [hi,h652,h653,dataValues_small _ hsmall]
  · simp only [hi,false_and,ite_false,Function.update_of_ne h653,Function.update_of_ne h652]
    rw [←writeParts_dataValues]
    simp only [writeParts,Function.update_apply,returned]
    split_ifs <;> rfl

theorem finishCall_literalWidth (target : ℕ) : ∀a∈finishCall target,a.literalWidth=0 := by
  intro a ha
  rcases List.mem_append.mp ha with ho|hz
  · simp only [Phase.copyOutput,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl <;> rfl
  · exact NatAssign.clearList_literalWidth privateTapes a hz

theorem returned_ready (S : Finset ℕ) (Q N : ℕ) (v : ℕ→Parts) (t : Store)
    (h : NatAssign.Bank (allIds S) (initialValues Q N v) t.val) (hz : NatAssign.Scratch t.val) :
    Ready S v t ∧ Clean t.val ∧ Word t.val 652 Q ∧ Word t.val 653 N := by
  refine ⟨⟨?_,hz⟩,?_,?_,?_⟩
  · intro i hi
    have hn : i≠653 := fun he => parameter_outside S 653 (by omega) (he ▸ hi)
    have hq : i≠652 := fun he => parameter_outside S 652 (by omega) (he ▸ hi)
    simpa only [initialValues,parameters,Function.update_of_ne hn,Function.update_of_ne hq] using
      h i (Finset.mem_union_left _ hi)
  · intro i hi
    obtain ⟨hn,hi⟩ := Finset.mem_erase.mp hi
    obtain ⟨hq,hi⟩ := Finset.mem_erase.mp hi
    have hh := h i (Finset.mem_union_right _ hi)
    rw [initialValues,parameters,Function.update_of_ne hn,Function.update_of_ne hq,dataValues_small v (ids_small i hi)] at hh
    exact (zero_word_iff_blank _ _).mp hh
  · simpa only [initialValues,parameters,Function.update_of_ne (by decide : (652:ℕ)≠653),Function.update_self] using
      h 652 (Finset.mem_union_right _ (by decide))
  · simpa only [initialValues,parameters,Function.update_self] using h 653 (Finset.mem_union_right _ (by decide))

#print axioms finishCall_values
#print axioms returned_ready
end Maxwell.Continuum.RationalDataflow.Phase.Runtime
