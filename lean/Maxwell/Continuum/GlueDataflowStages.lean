import Maxwell.Continuum.GlueDataflowData
import Maxwell.Continuum.NatAssignExternalWord
import Maxwell.Continuum.NaturalBankStage

/-! Banks and fixed instruction stages for repeated runtime glue calls. -/
namespace Maxwell.Continuum.RationalDataflow.Glue
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

theorem allIds_ge (S : Finset ℕ) (i : ℕ) (hi : i∈allIds S) : 4 ≤ i := by
  rcases Finset.mem_union.mp hi with hi|hi
  · exact RationalDataflow.ids_ge S i hi
  · exact GlueMachine.Runtime.ids_ge i hi

theorem precision_outside (S : Finset ℕ) : 640∉RationalDataflow.ids S := by
  intro hi
  rcases Finset.mem_union.mp hi with hi|hi
  · obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hi
    have hp := positivePort_ge r
    have hn := negativePort_ge r
    have hd := denominatorPort_ge r
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hr
    omega
  · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hi
    omega

theorem valid_lift {S T : Finset ℕ} (hST : S⊆T) {a : NatAssign.Instruction}
    (h : a.Valid S) : a.Valid T := by
  cases a <;> first | exact hST h | exact ⟨hST h.1,hST h.2.1,h.2.2⟩

theorem prepare_valid (S : Finset ℕ) (source : ℕ) (hs : source∈S) :
    ∀a∈prepareInverse source,a.Valid (allIds S) :=
  fun a ha => valid_lift Finset.subset_union_left (prepareInverse_valid S source hs a ha)

theorem prepare_values (N : ℕ) (v : ℕ→Parts) (source : ℕ) :
    NatAssign.values (prepareInverse source) (initialValues N v)=
      Function.update (beforeInverse v source) 640 N := by
  rw [initialValues,NatAssign.values_update_outside (RationalDataflow.ids {source}) _
    (prepareInverse_valid {source} source (by simp)) _ 640 N (precision_outside {source}),
    prepareInverse_values]

theorem prepareCall_valid (S : Finset ℕ) (source : ℕ) (hs : source∈S) :
    ∀a∈prepareCall source,a.Valid (allIds S) := by
  have hd := cell_mem hs (show denominatorPort source∈cellPorts source by simp [cellPorts])
  have hsmall (i : ℕ) (hi : i∈GlueMachine.Runtime.ids) : i∈allIds S := Finset.mem_union_right _ hi
  have hden : denominatorPort source∈allIds S := Finset.mem_union_left _ hd
  have hg := denominatorPort_ge source
  simp [prepareCall,clearMagnitude,NatAssign.Instruction.Valid,hden,
    hsmall 30 (by decide),hsmall 31 (by decide),hsmall 32 (by decide),hsmall 33 (by decide),
    hsmall 34 (by decide),hsmall 35 (by decide),hsmall 36 (by decide),hsmall 600 (by decide),
    hsmall 601 (by decide)]
  omega

theorem finishCall_valid (S : Finset ℕ) (target : ℕ) (ht : target∈S) :
    ∀a∈finishCall target,a.Valid (allIds S) := by
  have hp := Finset.mem_union_left GlueMachine.Runtime.ids
    (cell_mem ht (show positivePort target∈cellPorts target by simp [cellPorts]))
  have hn := Finset.mem_union_left GlueMachine.Runtime.ids
    (cell_mem ht (show negativePort target∈cellPorts target by simp [cellPorts]))
  have hd := Finset.mem_union_left GlueMachine.Runtime.ids
    (cell_mem ht (show denominatorPort target∈cellPorts target by simp [cellPorts]))
  have hsmall (i : ℕ) (hi : i∈GlueMachine.Runtime.ids) : i∈allIds S := Finset.mem_union_right _ hi
  intro a ha
  rcases List.mem_append.mp ha with hc|hz
  · have hpg := positivePort_ge target
    have hng := negativePort_ge target
    have hdg := denominatorPort_ge target
    simp only [copyOutput,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl
    · exact ⟨hsmall 602 (by decide),hp,by omega⟩
    · exact ⟨hsmall 603 (by decide),hn,by omega⟩
    · exact ⟨hsmall 604 (by decide),hd,by omega⟩
  · exact NatAssign.clearList_valid _ _ (fun i hi => hsmall i ((privateTapes_mem i).mp hi).1) a hz

theorem initial_bank (S : Finset ℕ) (N : ℕ) (v : ℕ→Parts) (s : Store) (hs : Ready S v s)
    (hz : Clean s.val) (hN : Word s.val 640 N) :
    NatAssign.Bank (allIds S) (initialValues N v) s.val := by
  intro i hi
  by_cases he : i=640
  · subst i;simpa only [initialValues,Function.update_self] using hN
  · simp only [initialValues,Function.update_of_ne he]
    rcases Finset.mem_union.mp hi with hr|hp
    · exact hs.1 i hr
    · rw [dataValues_small v (ids_small i hp)]
      exact (zero_word_iff_blank _ _).mpr (hz i (Finset.mem_erase.mpr ⟨he,hp⟩))

theorem initial_width (S : Finset ℕ) (N : ℕ) (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v)
    (hN : N.bits.length≤W) (i : ℕ) (hi : i∈allIds S) : (initialValues N v i).bits.length≤W := by
  by_cases he : i=640
  · subst i;simpa only [initialValues,Function.update_self] using hN
  · simp only [initialValues,Function.update_of_ne he]
    rcases Finset.mem_union.mp hi with hr|hp
    · exact dataValues_width S v W hw i hr
    · rw [dataValues_small v (ids_small i hp)];simp

theorem afterMagnitude_width (S : Finset ℕ) (N : ℕ) (v : ℕ→Parts) (source W : ℕ)
    (hs : source∈S) (hw : WidthBank S W v) (hN : N.bits.length≤W)
    (i : ℕ) (hi : i∈allIds S) :
    (Function.update (afterInverseMagnitude v source) 640 N i).bits.length≤W+1 := by
  by_cases he : i=640
  · subst i;simp only [Function.update_self];omega
  · simp only [Function.update_of_ne he]
    by_cases hr : i∈RationalDataflow.ids S
    · exact afterInverseMagnitude_width S v source hs W hw i hr
    · have hp := (Finset.mem_union.mp hi).resolve_left hr
      have hsmall := ids_small i hp
      have h30 : i≠30 := by intro hh;subst i;exact hr (magnitude_subset S (by decide))
      have h31 : i≠31 := by intro hh;subst i;exact hr (magnitude_subset S (by decide))
      have h34 : i≠34 := by intro hh;subst i;exact hr (magnitude_subset S (by decide))
      simp only [afterInverseMagnitude,beforeInverse,Function.update_of_ne h34,
        Function.update_of_ne h31,Function.update_of_ne h30,dataValues_small v hsmall]
      simp

theorem stage_executes (S : Finset ℕ) (ins : List NatAssign.Instruction)
    (hv : ∀a∈ins,a.Valid (allIds S)) (hl : ins.length≤25)
    (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈allIds S,(v i).bits.length≤B)
    (hc : ∀a∈ins,a.literalWidth≤B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank (allIds S) v s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t,Executes input tape (NatAssign.code ins) cost s t ∧ cost≤stageCost B ∧
      NatAssign.Bank (allIds S) (NatAssign.values ins v) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  exact fixedBankStage_executes (allIds S) (allIds_ge S) ins hv hl v B hw hc input tape s hs hz

#print axioms initial_bank
#print axioms stage_executes
end Maxwell.Continuum.RationalDataflow.Glue
