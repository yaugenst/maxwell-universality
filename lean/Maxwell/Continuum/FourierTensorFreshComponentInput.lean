import Maxwell.Continuum.FourierTensorComponentFootprint
import Maxwell.Cost.Structured.WordCopyPlan.Disjoint
import Maxwell.Cost.Structured.TapeBlockSwapFrame

/-! Install the actual mode descriptors and selected parameters in a fresh
disjoint component bank. The twelve runtime words are copied by charged
instructions; no rational bank or Fourier-row table is supplied. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.FreshComponent
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768

def gap (block : ℕ) : ℕ := 6000*(block+1)
def relocation (block : ℕ) : Equiv.Perm ℕ :=
  TapeBlockSwap.permutation 4 5996 (gap block) (by unfold gap;omega)
def sources : List ℕ := [210,212,213,214,215,350,351,352,354,355,710,711]
def ports : Finset ℕ := sources.toFinset
def plan (block : ℕ) : List (ℕ×ℕ) := sources.map (fun i=>(i,i+gap block))
def copyCode (block : ℕ) : Code := WordCopyPlan.code (plan block)

def words {n : ℕ} (a : Table n) (v : ℕ→ℕ) (i : ℕ) : List Bool :=
  if i=210 then a.width else if i=212 then a.basePositive else if i=213 then a.baseNegative
  else if i=214 then a.baseDenominator else if i=215 then a.clock else (v i).bits
def copyWidth {n : ℕ} (a : Table n) (v : ℕ→ℕ) : ℕ :=
  ModeAllocation.tableWidth a+∑i∈CalibrationStart.parameters,(v i).bits.length
def copyCost {n : ℕ} (a : Table n) (v : ℕ→ℕ) : ℕ := 12*(21*copyWidth a v+21)+1

def Fresh (block : ℕ) (s : BitRAMState) : Prop :=
  ∀i,4 ≤ i → i<6000 →s.tapes (i+gap block)=BitTape.blank

theorem sources_range (i : ℕ) (hi : i∈ports) : 4 ≤ i ∧ i<6000 := by
  simp only [ports,sources,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

theorem relocation_inside (block i : ℕ) (lo : 4 ≤ i) (hi : i<6000) :
    relocation block i=i+gap block := TapeBlockSwap.apply_inside _ _ _ _ i lo hi

theorem relocation_small (block i : ℕ) (hi : i<4) : relocation block i=i := by
  apply TapeBlockSwap.apply_outside
  · exact Or.inl hi
  · left;unfold gap;omega

theorem targets_eq (block : ℕ) : WordCopyPlan.targets (plan block)=ports.image (fun i=>i+gap block) := by
  ext i
  simp [WordCopyPlan.targets,plan,ports,List.map_map,Function.comp_def]

theorem words_bound {n : ℕ} (a : Table n) (v : ℕ→ℕ) (i : ℕ) (hi : i∈ports) :
    (words a v i).length≤copyWidth a v := by
  have descriptorBounds := ModeAllocation.tableWidth_spec a
  have parameter (j : ℕ) (hj : j∈CalibrationStart.parameters) : (v j).bits.length≤copyWidth a v :=
    (Finset.single_le_sum (fun k _=>Nat.zero_le (v k).bits.length) hj).trans (Nat.le_add_left _ _)
  simp only [ports,sources,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact descriptorBounds.width.trans (Nat.le_add_right _ _)
  · exact descriptorBounds.basePositive.trans (Nat.le_add_right _ _)
  · exact descriptorBounds.baseNegative.trans (Nat.le_add_right _ _)
  · exact descriptorBounds.baseDenominator.trans (Nat.le_add_right _ _)
  · exact descriptorBounds.clock.trans (Nat.le_add_right _ _)
  all_goals exact parameter _ (by decide)

structure Prepared (M A L R P Q N block : ℕ) (a : Table (2*aliasArraySize R)) (s : Store) : Prop where
  table : a.OutputReady (s.renameTapes (relocation block))
  selected : NatAssign.Bank CalibrationStart.parameters (CalibrationStart.parameterValues M A L R P Q N)
    (s.renameTapes (relocation block)).val
  headers : WordCleanup.Bounded CalibrationHandoff.targets 0 (s.renameTapes (relocation block)).val
  shared : WordCleanup.Bounded ZeroInitialization.clearPorts 0 (s.renameTapes (relocation block)).val
  scratch : WordCleanup.Bounded CalibrationStart.clearPorts 0 (s.renameTapes (relocation block)).val

theorem copy_executes (M A L R P Q N block : ℕ) (a : Table (2*aliasArraySize R))
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ha : a.OutputReady s)
    (selected : NatAssign.Bank CalibrationStart.parameters (CalibrationStart.parameterValues M A L R P Q N) s.val)
    (fresh : Fresh block s.val) :
    ∃cost t,Executes input tape (copyCode block) cost s t ∧
      cost≤copyCost a (CalibrationStart.parameterValues M A L R P Q N) ∧ Prepared M A L R P Q N block a t ∧
      BinaryPrecision.Frame (WordCopyPlan.targets (plan block)) s.val t.val := by
  let v := CalibrationStart.parameterValues M A L R P Q N
  let S := ports∪ports.image (fun i=>i+gap block)
  let initial : ℕ→List Bool := fun i=>if i∈ports then words a v i else []
  have separated : 6000≤gap block := by unfold gap;omega
  have sourceWords (i : ℕ) (hi : i∈ports) : BankArray.Word s.val i (words a v i) := by
    simp only [ports,sources,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ha.width
    · exact ha.basePositive
    · exact ha.baseNegative
    · exact ha.baseDenominator
    · exact ha.clock
    all_goals exact selected _ (by decide)
  have initialBank : WordCopyPlan.Bank S initial s.val := by
    intro i hi
    by_cases old : i∈ports
    · simpa only [initial,ite_eq_left old] using sourceWords i old
    · rw [show initial i=[] by exact ite_eq_right old]
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ((Finset.mem_union.mp hi).resolve_left old)
      exact ⟨0,by rw [fresh j (sources_range j hj).1 (sources_range j hj).2,BitTape.shifted_nil];rfl⟩
  have initialWidth : ∀i∈S,(initial i).length≤copyWidth a v := by
    intro i _
    by_cases hi : i∈ports
    · simpa only [initial,ite_eq_left hi] using words_bound a v i hi
    · simp only [initial,ite_eq_right hi,List.length_nil,Nat.zero_le]
  have valid : ∀x∈plan block,x.1∈S ∧ x.2∈S ∧ x.1≠x.2 := by
    intro x hx
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hx
    have member : i∈ports := List.mem_toFinset.mpr hi
    exact ⟨Finset.mem_union_left _ member,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,member,rfl⟩),by omega⟩
  obtain ⟨cost,t,run,hcost,bank,_,frame⟩ := WordCopyPlan.executes S (copyWidth a v) (plan block)
    valid initial initialWidth input tape s initialBank
  have copies := WordCopyPlan.evaluate_copies (plan block) (by
    simp only [plan,List.map_map,Function.comp_def]
    exact List.Nodup.map (fun i j h=>by omega) (by decide : sources.Nodup))
    (by
      intro x hx y hy
      obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hx
      obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hy
      have range:=sources_range j (List.mem_toFinset.mpr hj)
      omega) initial
  have localWord (i : ℕ) (hi : i∈ports) :
      BankArray.Word (t.renameTapes (relocation block)).val i (words a v i) := by
    have link : (i,i+gap block)∈plan block:=List.mem_map.mpr ⟨i,List.mem_toFinset.mp hi,rfl⟩
    have h:=bank (i+gap block) (valid _ link).2.1
    rw [copies _ link,show initial i=words a v i from ite_eq_left hi] at h
    obtain ⟨origin,h⟩:=h
    refine ⟨origin,?_⟩
    change t.val.tapes (relocation block i)=_
    rw [relocation_inside block i (sources_range i hi).1 (sources_range i hi).2]
    exact h
  have blank (i : ℕ) (lo : 4 ≤ i) (hi : i<6000) (outside : i∉ports) :
      Blank (t.renameTapes (relocation block)).val i := by
    have untouched : i+gap block∉WordCopyPlan.targets (plan block) := by
      rw [targets_eq]
      intro member
      obtain ⟨j,hj,equal⟩:=Finset.mem_image.mp member
      have : j=i := by omega
      exact outside (this ▸ hj)
    refine ⟨0,?_⟩
    change t.val.tapes (relocation block i)=_
    rw [relocation_inside block i lo hi,frame.tapes _ untouched,fresh i lo hi]
    rfl
  have low (i : ℕ) (hi : i<4) : Blank (t.renameTapes (relocation block)).val i := by
    have original : Blank s.val i := by
      interval_cases i
      · exact ha.scratch.1
      · exact ha.scratch.2.1
      · exact ha.scratch.2.2.1
      · exact ha.scratch.2.2.2.1
    apply RationalAccumulator.blank_of_eq (show (t.renameTapes (relocation block)).val.tapes i=s.val.tapes i from ?_) original
    change t.val.tapes (relocation block i)=_
    rw [relocation_small block i hi]
    apply frame.tapes
    rw [targets_eq]
    intro member
    obtain ⟨j,_,equal⟩:=Finset.mem_image.mp member
    omega
  have arrayScratch : BankArray.Scratch (t.renameTapes (relocation block)).val :=
    ⟨low 0 (by decide),low 1 (by decide),low 2 (by decide),low 3 (by decide),
      blank 5 (by decide) (by decide) (by decide),blank 6 (by decide) (by decide) (by decide),
      blank 8 (by decide) (by decide) (by decide),blank 9 (by decide) (by decide) (by decide)⟩
  have bounded (list : List ℕ) (range : ∀i∈list,i<6000 ∧ i∉ports) :
      WordCleanup.Bounded list 0 (t.renameTapes (relocation block)).val := by
    intro i hi
    have clear : Blank (t.renameTapes (relocation block)).val i := by
      by_cases small:i<4
      · exact low i small
      · exact blank i (by omega) (range i hi).1 (range i hi).2
    obtain ⟨origin,clear⟩:=clear
    exact ⟨[],le_rfl,origin,by simpa only [BitTape.shifted_nil] using clear⟩
  refine ⟨cost,t,run,?_,?_,frame⟩
  · simpa only [plan,List.length_map,show sources.length=12 from rfl,copyCost,v] using hcost
  · refine ⟨?_,?_,bounded _ (by decide),
      bounded _ (by simp only [ZeroInitialization.clearPorts,Finset.mem_sort];decide),
      bounded _ (by simp only [CalibrationStart.clearPorts,Finset.mem_sort];decide)⟩
    · refine ⟨arrayScratch,blank 7 (by decide) (by decide) (by decide),
        blank 37 (by decide) (by decide) (by decide),localWord 210 (by decide),
        localWord 212 (by decide),localWord 213 (by decide),localWord 214 (by decide),
        localWord 215 (by decide),?_,?_,?_⟩
      all_goals change BitArray.Represents t.val.memory _ _ _
      all_goals rw [frame.memory]
      · exact ha.positive
      · exact ha.negative
      · exact ha.denominator
    · intro i hi
      have member : i∈ports := (by decide : CalibrationStart.parameters⊆ports) hi
      have hh := localWord i member
      have outside : i≠210 ∧ i≠212 ∧ i≠213 ∧ i≠214 ∧ i≠215 := by
        simp only [CalibrationStart.parameters,Finset.mem_insert,Finset.mem_singleton] at hi
        omega
      simpa only [words,ite_eq_right outside.1,ite_eq_right outside.2.1,
        ite_eq_right outside.2.2.1,ite_eq_right outside.2.2.2.1,ite_eq_right outside.2.2.2.2,
        BankArray.Word,RationalAccumulator.Word,v] using hh

#print axioms copy_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.FreshComponent
