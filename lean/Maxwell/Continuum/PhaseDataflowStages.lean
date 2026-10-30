import Maxwell.Continuum.PhaseDataflowData
import Maxwell.Continuum.RationalDataflowProgram

/-! Shared-bank preparation and cleanup for literal phase evaluation. -/
namespace Maxwell.Continuum.RationalDataflow.Phase
open Maxwell.Cost Maxwell.Cost.Structured RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

theorem allIds_ge (S : Finset ℕ) (i : ℕ) (hi : i∈allIds S) : 4 ≤ i := by
  rcases Finset.mem_union.mp hi with h|h
  · exact RationalDataflow.ids_ge S i h
  · exact PhaseMachine.allIds_ge i h

private theorem valid_lift {S T : Finset ℕ} (hST : S⊆T) {a : NatAssign.Instruction}
    (h : a.Valid S) : a.Valid T := by
  cases a with
  | literal target value => exact hST h
  | copy source target => exact ⟨hST h.1,hST h.2.1,h.2.2⟩
  | add source target => exact ⟨hST h.1,hST h.2.1,h.2.2⟩
  | multiply source target => exact ⟨hST h.1,hST h.2.1,h.2.2⟩

theorem prepare_valid (S : Finset ℕ) (source : ℕ) (hs : source∈S) :
    ∀a∈prepareInverse source,a.Valid (allIds S) :=
  fun a ha => valid_lift Finset.subset_union_left (prepareInverse_valid S source hs a ha)

theorem prepareCall_valid (S : Finset ℕ) (source : ℕ) (hs : source∈S) :
    ∀a∈prepareCall source,a.Valid (allIds S) := by
  have hd := cell_mem hs (show denominatorPort source∈cellPorts source by simp [cellPorts])
  have hsmall (i : ℕ) (hi : i∈PhaseMachine.allIds) : i∈allIds S := Finset.mem_union_right _ hi
  have hden : denominatorPort source∈allIds S := Finset.mem_union_left _ hd
  have hg := denominatorPort_ge source
  simp [prepareCall,clearMagnitude,NatAssign.Instruction.Valid,hden,
    hsmall 30 (by decide),hsmall 31 (by decide),hsmall 32 (by decide),hsmall 33 (by decide),
    hsmall 34 (by decide),hsmall 35 (by decide),hsmall 36 (by decide),hsmall 630 (by decide),
    hsmall 631 (by decide)]
  omega

theorem finishCall_valid (S : Finset ℕ) (target : ℕ) (ht : target∈S) :
    ∀a∈finishCall target,a.Valid (allIds S) := by
  have hp := Finset.mem_union_left PhaseMachine.allIds
    (cell_mem ht (show positivePort target∈cellPorts target by simp [cellPorts]))
  have hn := Finset.mem_union_left PhaseMachine.allIds
    (cell_mem ht (show negativePort target∈cellPorts target by simp [cellPorts]))
  have hd := Finset.mem_union_left PhaseMachine.allIds
    (cell_mem ht (show denominatorPort target∈cellPorts target by simp [cellPorts]))
  have hsmall (i : ℕ) (hi : i∈PhaseMachine.allIds) : i∈allIds S := Finset.mem_union_right _ hi
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
  · exact NatAssign.clearList_valid _ _ (fun i hi => hsmall i ((privateTapes_mem i).mp hi)) a hz

theorem initial_bank (S : Finset ℕ) (v : ℕ→Parts) (s : Store) (hs : Ready S v s) (hz : Clean s.val) :
    NatAssign.Bank (allIds S) (dataValues v) s.val := by
  intro i hi
  rcases Finset.mem_union.mp hi with hr|hp
  · exact hs.1 i hr
  · rw [dataValues_small v (PhaseMachine.allIds_small i hp)]
    exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (hz i hp)

theorem initial_width (S : Finset ℕ) (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v)
    (i : ℕ) (hi : i∈allIds S) : (dataValues v i).bits.length≤W := by
  rcases Finset.mem_union.mp hi with hr|hp
  · exact dataValues_width S v W hw i hr
  · rw [dataValues_small v (PhaseMachine.allIds_small i hp)]
    simp

theorem afterMagnitude_width (S : Finset ℕ) (v : ℕ→Parts) (source W : ℕ) (hs : source∈S)
    (hw : WidthBank S W v) (i : ℕ) (hi : i∈allIds S) :
    (afterInverseMagnitude v source i).bits.length≤W+1 := by
  by_cases hr : i∈RationalDataflow.ids S
  · exact afterInverseMagnitude_width S v source hs W hw i hr
  · have hp := (Finset.mem_union.mp hi).resolve_left hr
    have hsmall := PhaseMachine.allIds_small i hp
    have h30 : i≠30 := by intro he;subst i;exact hr (magnitude_subset S (by decide))
    have h31 : i≠31 := by intro he;subst i;exact hr (magnitude_subset S (by decide))
    have h34 : i≠34 := by intro he;subst i;exact hr (magnitude_subset S (by decide))
    simp only [afterInverseMagnitude,beforeInverse,Function.update_of_ne h34,
      Function.update_of_ne h31,Function.update_of_ne h30,dataValues_small v hsmall]
    simp

theorem seeded_width (S : Finset ℕ) (v : ℕ→Parts) (source W : ℕ) (hs : source∈S)
    (hw : WidthBank S W v) (i : ℕ) (hi : i∈allIds S) : (seeded v source i).bits.length≤W+1 := by
  by_cases hsmall : i<1000
  · rw [seeded_small v source i hsmall]
    unfold PhaseMachine.initialValues
    split_ifs
    · exact (IntegerNormSquare.magnitude_bits_length_le _ _).trans
        (Nat.add_le_add_right (max_le (hw source hs).1 (hw source hs).2.1) 1)
    · exact (hw source hs).2.2.trans (Nat.le_succ W)
    · simp
  · rw [seeded_large v source i (by omega)]
    exact (initial_width S v W hw i hi).trans (Nat.le_succ W)

def workWidth (Q N W : ℕ) : ℕ := W+1+PhaseMachine.fullFinalWidth Q N (W+1)

theorem returned_width (S : Finset ℕ) (base : ℕ→Sign) (Q N : ℕ) (v : ℕ→Parts)
    (source W : ℕ) (hs : source∈S) (hw : WidthBank S W v) (i : ℕ) (hi : i∈allIds S) :
    (returned base Q N v source i).bits.length≤workWidth Q N W := by
  unfold returned
  split_ifs with hp
  · have hm : (magnitude (v source)).bits.length≤W+1 :=
      (IntegerNormSquare.magnitude_bits_length_le _ _).trans
        (Nat.add_le_add_right (max_le (hw source hs).1 (hw source hs).2.1) 1)
    exact (PhaseMachine.fullFinal_width _ _ _ _ _ _ _ hm ((hw source hs).2.2.trans (Nat.le_succ W)) i hp).trans
      (by unfold workWidth;omega)
  · exact (initial_width S v W hw i hi).trans (by unfold workWidth;omega)

#print axioms prepareCall_valid
#print axioms finishCall_valid
#print axioms returned_width
end Maxwell.Continuum.RationalDataflow.Phase
