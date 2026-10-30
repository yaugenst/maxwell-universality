import Maxwell.Continuum.PhaseRuntimeDataflowData
import Maxwell.Continuum.RationalDataflowProgram

/-! Exact banks, raw-word widths, and charged fixed arithmetic stages for
the shared runtime phase call. -/
namespace Maxwell.Continuum.RationalDataflow.Phase.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def stageCost (B : ℕ) : ℕ := 2^180*(B+2)^2
def workWidth (Q N W : ℕ) : ℕ := 2^68*(Q+N+W+12)^4

theorem allIds_ge (S : Finset ℕ) (i : ℕ) (hi : i∈allIds S) : 4 ≤ i := by
  rcases Finset.mem_union.mp hi with hi|hi
  · exact RationalDataflow.ids_ge S i hi
  · exact PhaseMachine.Runtime.ids_ge i hi

private theorem valid_lift {S T : Finset ℕ} (hST : S⊆T) {a : NatAssign.Instruction}
    (h : a.Valid S) : a.Valid T := by
  cases a <;> first | exact hST h | exact ⟨hST h.1,hST h.2.1,h.2.2⟩

theorem prepare_valid (S : Finset ℕ) (source : ℕ) (hs : source∈S) :
    ∀a∈prepareInverse source,a.Valid (allIds S) :=
  fun a ha => valid_lift Finset.subset_union_left (prepareInverse_valid S source hs a ha)

theorem prepareCall_valid (S : Finset ℕ) (source : ℕ) (hs : source∈S) :
    ∀a∈prepareCall source,a.Valid (allIds S) := by
  have hd := cell_mem hs (show denominatorPort source∈cellPorts source by simp [cellPorts])
  have hsmall (i : ℕ) (hi : i∈PhaseMachine.Runtime.ids) : i∈allIds S := Finset.mem_union_right _ hi
  have hden : denominatorPort source∈allIds S := Finset.mem_union_left _ hd
  have hg := denominatorPort_ge source
  simp [prepareCall,clearMagnitude,NatAssign.Instruction.Valid,hden,
    hsmall 30 (by decide),hsmall 31 (by decide),hsmall 32 (by decide),hsmall 33 (by decide),
    hsmall 34 (by decide),hsmall 35 (by decide),hsmall 36 (by decide),hsmall 650 (by decide),hsmall 651 (by decide)]
  omega

theorem finishCall_valid (S : Finset ℕ) (target : ℕ) (ht : target∈S) :
    ∀a∈finishCall target,a.Valid (allIds S) := by
  have hp := Finset.mem_union_left PhaseMachine.Runtime.ids
    (cell_mem ht (show positivePort target∈cellPorts target by simp [cellPorts]))
  have hn := Finset.mem_union_left PhaseMachine.Runtime.ids
    (cell_mem ht (show negativePort target∈cellPorts target by simp [cellPorts]))
  have hd := Finset.mem_union_left PhaseMachine.Runtime.ids
    (cell_mem ht (show denominatorPort target∈cellPorts target by simp [cellPorts]))
  have hsmall (i : ℕ) (hi : i∈PhaseMachine.Runtime.ids) : i∈allIds S := Finset.mem_union_right _ hi
  intro a ha
  rcases List.mem_append.mp ha with hc|hz
  · have hpg := positivePort_ge target
    have hng := negativePort_ge target
    have hdg := denominatorPort_ge target
    simp only [Phase.copyOutput,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl
    · exact ⟨hsmall 602 (by decide),hp,by omega⟩
    · exact ⟨hsmall 603 (by decide),hn,by omega⟩
    · exact ⟨hsmall 604 (by decide),hd,by omega⟩
  · exact NatAssign.clearList_valid _ _ (fun i hi => hsmall i ((privateTapes_mem i).mp hi).1) a hz

theorem initial_bank (S : Finset ℕ) (Q N : ℕ) (v : ℕ→Parts) (s : Store) (hs : Ready S v s)
    (hz : Clean s.val) (hQ : Word s.val 652 Q) (hN : Word s.val 653 N) :
    NatAssign.Bank (allIds S) (initialValues Q N v) s.val := by
  intro i hi
  by_cases h653 : i=653
  · subst i;simpa only [initialValues,parameters,Function.update_self] using hN
  by_cases h652 : i=652
  · subst i;simpa only [initialValues,parameters,Function.update_of_ne (by decide : (652:ℕ)≠653),Function.update_self] using hQ
  simp only [initialValues,parameters,Function.update_of_ne h653,Function.update_of_ne h652]
  rcases Finset.mem_union.mp hi with hr|hp
  · exact hs.1 i hr
  · rw [dataValues_small v (ids_small i hp)]
    exact (zero_word_iff_blank _ _).mpr (hz i (Finset.mem_erase.mpr ⟨h653,Finset.mem_erase.mpr ⟨h652,hp⟩⟩))

theorem initial_width (S : Finset ℕ) (Q N : ℕ) (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) (i : ℕ) (hi : i∈allIds S) :
    (initialValues Q N v i).bits.length≤W := by
  by_cases h653 : i=653
  · subst i;simpa only [initialValues,parameters,Function.update_self] using hN
  by_cases h652 : i=652
  · subst i;simpa only [initialValues,parameters,Function.update_of_ne (by decide : (652:ℕ)≠653),Function.update_self] using hQ
  simp only [initialValues,parameters,Function.update_of_ne h653,Function.update_of_ne h652]
  rcases Finset.mem_union.mp hi with hr|hp
  · exact dataValues_width S v W hw i hr
  · rw [dataValues_small v (ids_small i hp)];simp

theorem afterMagnitude_width (S : Finset ℕ) (Q N : ℕ) (v : ℕ→Parts) (source W : ℕ)
    (hs : source∈S) (hw : WidthBank S W v) (hQ : Q.bits.length≤W) (hN : N.bits.length≤W)
    (i : ℕ) (hi : i∈allIds S) :
    (parameters Q N (afterInverseMagnitude v source) i).bits.length≤W+1 := by
  by_cases h653 : i=653
  · subst i;simp only [parameters,Function.update_self];omega
  by_cases h652 : i=652
  · subst i;simp only [parameters,Function.update_of_ne (by decide : (652:ℕ)≠653),Function.update_self];omega
  simp only [parameters,Function.update_of_ne h653,Function.update_of_ne h652]
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

theorem returned_width (S : Finset ℕ) (base : RationalTaylor.Runtime.Cycle) (Q N : ℕ)
    (v : ℕ→Parts) (source W : ℕ) (hs : source∈S) (hw : WidthBank S W v)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) (i : ℕ) (hi : i∈allIds S) :
    (returned base Q N v source i).bits.length≤workWidth Q N W := by
  unfold returned
  split_ifs with hp
  · have hm : (Phase.magnitude (v source)).bits.length≤W+1 :=
      (IntegerNormSquare.magnitude_bits_length_le _ _).trans
        (Nat.add_le_add_right (max_le (hw source hs).1 (hw source hs).2.1) 1)
    have h := PhaseMachine.Runtime.finalValues_width_polynomial (Phase.negative (v source)) base
      (Phase.magnitude (v source)) (v source).denominator Q N (W+1) i hp hm
      ((hw source hs).2.2.trans (by omega)) (hQ.trans (by omega)) (hN.trans (by omega))
    exact h.trans (by
      unfold workWidth PhaseMachine.sizeParameter
      exact Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by omega) 4))
  · have hr := (Finset.mem_union.mp hi).resolve_right hp
    have hh : W≤(Q+N+W+12)^4 := (show W≤Q+N+W+12 by omega).trans (Nat.le_self_pow (by decide) _)
    exact (dataValues_width S v W hw i hr).trans (hh.trans (Nat.le_mul_of_pos_left _ (by norm_num)))

theorem stage_executes (S : Finset ℕ) (ins : List NatAssign.Instruction)
    (hv : ∀a∈ins,a.Valid (allIds S)) (hl : ins.length≤50)
    (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈allIds S,(v i).bits.length≤B)
    (hc : ∀a∈ins,a.literalWidth≤B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank (allIds S) v s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (NatAssign.code ins) cost s t ∧ cost≤stageCost B ∧
      NatAssign.Bank (allIds S) (NatAssign.values ins v) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨c,t,e,hc0,bt,zt,ft⟩ := NatAssign.executes (allIds S) (allIds_ge S) ins hv v input tape s hs hz
  have hp := NatAssign.price_bound (allIds S) ins hv v B hw hc
  have hcoef : 3000*8^ins.length≤(2:ℕ)^180 := by
    calc
      _≤3000*8^50 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hl)
      _≤_ := by norm_num
  refine ⟨c,t,e,hc0.trans (hp.trans (Nat.mul_le_mul_right _ hcoef)),bt,zt,ft.mono ?_⟩
  intro i hi
  rcases Finset.mem_union.mp hi with hi|hi
  · exact Finset.mem_union_left _ hi
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    apply Finset.mem_union_right
    have h := hv a ha
    cases a <;> first | exact h | exact h.2.1

#print axioms returned_width
#print axioms stage_executes
end Maxwell.Continuum.RationalDataflow.Phase.Runtime
