import Maxwell.Continuum.StoredAmbientMachine
import Maxwell.Continuum.StoredGeometryCoordinate
import Maxwell.Cost.Structured.TapeBlockSwapFrame
import Maxwell.Cost.Structured.WordCleanup

/-! Serialize the ambient cubes beside retained rational and table tapes.
Only the original ambient iterator bank is relocated; actual old words in
the destination bank are cleared by charged scans. -/
namespace Maxwell.Continuum.StoredAmbient
open Maxwell.Cost Maxwell.Cost.Structured RationalAccumulator
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def relocation : Equiv.Perm ℕ := TapeBlockSwap.permutation 240 19 4760 (by decide)
def relocatedOld : List ℕ := [5000,5001,5002,5010,5011,5012,5013,5014,5015,5016,5017,5018]
def relocatedWork : Finset ℕ := {0,1,2,3}∪relocatedOld.toFinset
def initial (v : ℕ→ℕ) (i : ℕ) : ℕ := if i∈outputs then 0 else v i
def relocatedCode : Code := .seq (WordCleanup.code relocatedOld) (.call (code.compile.renameTapes relocation))
def relocatedCost (v : ℕ→ℕ) (B H : ℕ) : ℕ := 12*(6*H+4)+1+cost v B+1

theorem relocation_inputs (i : ℕ) (hi : i∈inputs) : relocation i=i := by
  apply TapeBlockSwap.apply_outside
  all_goals simp only [inputs,Finset.mem_insert,Finset.mem_singleton] at hi
  all_goals omega

theorem initial_inputs (v : ℕ→ℕ) (i : ℕ) (hi : i∈inputs) : initial v i=v i := by
  apply ite_eq_right
  exact fun ho=>Finset.disjoint_left.mp (by decide : Disjoint inputs outputs) hi ho

theorem initial_side (v : ℕ→ℕ) : side (initial v)=side v := by
  funext j
  unfold side
  rw [initial_inputs v _ (by fin_cases j <;> decide),initial_inputs v 2221 (by decide),
    initial_inputs v 2244 (by decide)]

theorem relocation_small (i : ℕ) (hi : i<4) : relocation i=i :=
  TapeBlockSwap.apply_outside 240 19 4760 (by decide) i (Or.inl (by omega)) (Or.inl (by omega))

theorem relocated_executes (v : ℕ→ℕ) (B H : ℕ) (hB : 3≤B)
    (width : ∀i∈inputs,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank inputs v s.val) (scratch : NatAssign.Scratch s.val)
    (old : WordCleanup.Bounded relocatedOld H s.val) :
    ∃steps t,Executes input tape relocatedCode steps s t ∧ steps≤relocatedCost v B H ∧
      t.val.output=(AmbientEncoding.bits (side v 0) (side v 1) (side v 2)).reverse++s.val.output ∧
      NatAssign.Scratch t.val ∧GeometryOutput.OutputFrame relocatedWork s.val t.val := by
  obtain ⟨c,a,e,hc,blank,frame⟩:=WordCleanup.executes relocatedOld H input tape s old
  have renamed_tape (i : ℕ) : (a.renameTapes relocation).val.tapes i=a.val.tapes (relocation i):=rfl
  have words : NatAssign.Bank ids (initial v) (a.renameTapes relocation).val := by
    intro i hi
    by_cases ho : i∈outputs
    · rw [initial,ite_eq_left ho]
      apply (zero_word_iff_blank _ _).mpr
      apply blank_of_eq (renamed_tape i) (blank (relocation i) ?_)
      have inside : relocation i=i+4760 := by
        apply TapeBlockSwap.apply_inside
        all_goals simp only [outputs,Finset.mem_insert,Finset.mem_singleton] at ho
        all_goals omega
      rw [inside]
      simp only [outputs,Finset.mem_insert,Finset.mem_singleton] at ho
      simp only [relocatedOld,List.mem_cons,List.not_mem_nil,or_false]
      omega
    · have hin : i∈inputs := (Finset.mem_union.mp hi).resolve_right ho
      rw [initial_inputs v i hin]
      apply word_of_eq ((renamed_tape i).trans (congrArg a.val.tapes (relocation_inputs i hin)))
      apply word_of_eq (frame.tapes i ?_) (bank i hin)
      exact Finset.disjoint_left.mp (by decide : Disjoint inputs relocatedOld.toFinset) hin
  have widths : ∀i∈ids,(initial v i).bits.length≤B := by
    intro i hi
    by_cases ho:i∈outputs
    · simp [initial,ho]
    · rw [initial,ite_eq_right ho]
      exact width i ((Finset.mem_union.mp hi).resolve_right ho)
  have scratchA : NatAssign.Scratch (a.renameTapes relocation).val := by
    intro i hi
    apply blank_of_eq ((renamed_tape i).trans (congrArg a.val.tapes (relocation_small i hi)))
    apply blank_of_eq (frame.tapes i ?_) (scratch i hi)
    simp only [relocatedOld,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    omega
  obtain ⟨d,b,eb,hd,out,_,zb,_,memory,head,random,keep⟩:=executes (initial v) B hB widths
    input tape (a.renameTapes relocation) words scratchA
  have run:=eb.renamed_call relocation
  have double : (a.renameTapes relocation).renameTapes relocation=a:=Store.renameTapes_symm relocation a
  rw [double] at run
  refine ⟨c+(d+1),b.renameTapes relocation,e.seq run,?_,?_,?_,?_⟩
  · have cost_eq : cost (initial v) B=cost v B:=by unfold cost;rw [initial_side]
    rw [cost_eq] at hd
    change c≤12*(6*H+4)+1 at hc
    unfold relocatedCost
    omega
  · change b.val.output=_
    rw [out,initial_side]
    change _++a.val.output=_
    rw [frame.output]
  · intro i hi
    exact blank_of_eq ((show (b.renameTapes relocation).val.tapes i=b.val.tapes (relocation i) from rfl).trans
      (congrArg b.val.tapes (relocation_small i hi))) (zb i hi)
  · refine ⟨memory.trans frame.memory,head.trans frame.inputHead,random.trans frame.randomCursor,?_⟩
    intro i hi
    have notUsed : relocation i∉work := by
      have image_eq : work.image relocation=relocatedWork := by decide +kernel
      intro member
      apply hi
      rw [←image_eq]
      exact Finset.mem_image.mpr ⟨relocation i,member,
        TapeBlockSwap.involutive 240 19 4760 (by decide) i⟩
    change b.val.tapes (relocation i)=s.val.tapes i
    rw [keep _ notUsed]
    change a.val.tapes (relocation (relocation i))=s.val.tapes i
    have inv : relocation (relocation i)=i := TapeBlockSwap.involutive 240 19 4760 (by decide) i
    rw [inv]
    exact frame.tapes i (fun ho=>hi (Finset.mem_union_right _ ho))

#print axioms relocated_executes
end Maxwell.Continuum.StoredAmbient
