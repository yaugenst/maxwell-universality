import Maxwell.Continuum.DyadicFloorData
import Maxwell.Continuum.NatAssignOutputWidth
import Maxwell.Continuum.RationalDataflowArray

/-! Concrete banks and raw-word bounds for dyadic floor evaluation. -/
namespace Maxwell.Continuum.RationalDataflow.DyadicFloor
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem allIds_ge (S : Finset ℕ) (i : ℕ) (hi : i∈allIds S) : 10 ≤ i := by
  rcases Finset.mem_union.mp hi with hr|hq
  · rcases Finset.mem_union.mp hr with hr|he
    · exact ids_ge_ten S i hr
    · simp only [extraIds,Finset.mem_insert,Finset.mem_singleton] at he
      omega
  · simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hq
    omega

theorem logical_mem (S : Finset ℕ) (i : ℕ) (hi : i∈ids S) : i∈allIds S :=
  Finset.mem_union_left _ (Finset.mem_union_left _ hi)
theorem extra_mem (S : Finset ℕ) (i : ℕ) (hi : i∈extraIds) : i∈allIds S :=
  Finset.mem_union_left _ (Finset.mem_union_right _ hi)
theorem magnitude_mem (S : Finset ℕ) : RationalMagnitude.ids⊆allIds S :=
  fun i hi => logical_mem S i (magnitude_subset S hi)

theorem prepare_valid (S : Finset ℕ) (P source : ℕ) (hs : source∈S) :
    ∀a∈prepare P source,a.Valid (allIds S) := by
  have hp := logical_mem S _ (cell_mem hs (show positivePort source∈cellPorts source by simp [cellPorts]))
  have hn := logical_mem S _ (cell_mem hs (show negativePort source∈cellPorts source by simp [cellPorts]))
  have hd := logical_mem S _ (cell_mem hs (show denominatorPort source∈cellPorts source by simp [cellPorts]))
  have hpg := positivePort_ge source
  have hng := negativePort_ge source
  have hdg := denominatorPort_ge source
  simp [prepare,NatAssign.Instruction.Valid,hp,hn,hd,
    magnitude_mem S (show 30∈RationalMagnitude.ids by decide),
    magnitude_mem S (show 31∈RationalMagnitude.ids by decide),
    extra_mem S 140 (by decide),extra_mem S 142 (by decide),extra_mem S 143 (by decide)]
  omega

theorem finish_valid (S : Finset ℕ) (target : ℕ) (ht : target∈S) :
    ∀a∈finish target,a.Valid (allIds S) := by
  have hp := logical_mem S _ (cell_mem ht (show positivePort target∈cellPorts target by simp [cellPorts]))
  have hn := logical_mem S _ (cell_mem ht (show negativePort target∈cellPorts target by simp [cellPorts]))
  have hd := logical_mem S _ (cell_mem ht (show denominatorPort target∈cellPorts target by simp [cellPorts]))
  have hpg := positivePort_ge target
  have hng := negativePort_ge target
  intro a ha
  rcases List.mem_append.mp ha with ho|hz
  · simp only [output,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl
    · exact ⟨extra_mem S 140 (by decide),hp,by omega⟩
    · exact ⟨magnitude_mem S (show 31∈RationalMagnitude.ids by decide),hn,by omega⟩
    · exact hd
  · apply NatAssign.clearList_valid _ _ _ a hz
    intro i hi
    have hm : i∈RationalMagnitude.ids ∨ i∈extraIds := by
      simp only [privateTapes,List.mem_cons,List.not_mem_nil,or_false] at hi
      simp only [RationalMagnitude.ids,extraIds,Finset.mem_insert,Finset.mem_singleton]
      tauto
    exact hm.elim (fun h => magnitude_mem S h) (extra_mem S i)

theorem extra_small (i : ℕ) (hi : i∈extraIds∪NaturalQuotient.workPorts) : i<1000 := by
  simp only [extraIds,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem initial_bank (S : Finset ℕ) (v : ℕ→Parts) (s : Store) (hs : Ready S v s) (hz : Clean s.val) :
    NatAssign.Bank (allIds S) (dataValues v) s.val := by
  intro i hi
  by_cases hr : i∈ids S
  · exact hs.1 i hr
  · have he : i∈extraIds∪NaturalQuotient.workPorts := by
      simpa only [allIds,Finset.mem_union,hr,false_or] using hi
    rw [dataValues_small v (extra_small i he)]
    exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (hz.2 i he)

theorem initial_width (S : Finset ℕ) (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v)
    (i : ℕ) (hi : i∈allIds S) : (dataValues v i).bits.length≤W := by
  by_cases hr : i∈ids S
  · exact dataValues_width S v W hw i hr
  · have he : i∈extraIds∪NaturalQuotient.workPorts := by
      simpa only [allIds,Finset.mem_union,hr,false_or] using hi
    rw [dataValues_small v (extra_small i he)]
    simp

theorem prepare_literalWidth (P source : ℕ) : ∀a∈prepare P source,a.literalWidth≤P+1 := by
  have hp : (2^P:ℕ).bits.length=P+1 := by rw [Nat.size_eq_bits_len,Nat.size_pow]
  simp [prepare,NatAssign.Instruction.literalWidth,hp]

def workWidth (P W : ℕ) : ℕ := 2^12*(P+W+3)

theorem beforeMagnitude_width (S : Finset ℕ) (P : ℕ) (v : ℕ→Parts) (source W : ℕ)
    (hs : source∈S) (hw : WidthBank S W v) (i : ℕ) (hi : i∈allIds S) :
    (beforeMagnitude P v source i).bits.length≤2^10*(P+W+2) := by
  have h := NatAssign.values_width_bound (allIds S) (prepare P source) (prepare_valid S P source hs)
    (dataValues v) (P+W+1) (fun i hi => (initial_width S v W hw i hi).trans (by omega))
    (fun a ha => (prepare_literalWidth P source a ha).trans (by omega)) i hi
  rw [prepare_values] at h
  simpa only [show (prepare P source).length=10 by rfl] using (Nat.le_add_right _ 1).trans h

theorem afterMagnitude_width (S : Finset ℕ) (P : ℕ) (v : ℕ→Parts) (source W : ℕ)
    (hs : source∈S) (hw : WidthBank S W v) (hx : (v source).Valid)
    (i : ℕ) (hi : i∈allIds S) : (afterMagnitude P v source i).bits.length≤workWidth P W := by
  by_cases he : i=34
  · subst i
    simp only [afterMagnitude,Function.update_self]
    rw [←magnitude_eq P (v source) hx]
    have hp := beforeMagnitude_width S P v source W hs hw 30 (magnitude_mem S (by decide))
    have hn := beforeMagnitude_width S P v source W hs hw 31 (magnitude_mem S (by decide))
    rw [(beforeMagnitude_inputs P v source).1] at hp
    rw [(beforeMagnitude_inputs P v source).2.1] at hn
    apply (IntegerNormSquare.magnitude_bits_length_le _ _).trans
    unfold workWidth
    omega
  · simp only [afterMagnitude,Function.update_of_ne he]
    apply (beforeMagnitude_width S P v source W hs hw i hi).trans
    unfold workWidth
    omega

theorem divided_width (S : Finset ℕ) (P : ℕ) (v : ℕ→Parts) (source W : ℕ)
    (hs : source∈S) (hw : WidthBank S W v) (hx : (v source).Valid)
    (i : ℕ) (hi : i∈allIds S) : (divided P v source i).bits.length≤workWidth P W := by
  by_cases he : i=140
  · subst i
    simp only [divided,Function.update_self]
    have hn := afterMagnitude_width S P v source W hs hw hx 34 (magnitude_mem S (by decide))
    simp only [afterMagnitude,Function.update_self] at hn
    rw [Nat.size_eq_bits_len] at hn ⊢
    exact (Nat.size_le_size (Nat.div_le_self _ _)).trans hn
  · simp only [divided,Function.update_of_ne he]
    exact afterMagnitude_width S P v source W hs hw hx i hi

#print axioms prepare_valid
#print axioms divided_width
end Maxwell.Continuum.RationalDataflow.DyadicFloor
