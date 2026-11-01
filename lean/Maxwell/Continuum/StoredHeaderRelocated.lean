import Maxwell.Continuum.StoredHeaderMachine
import Maxwell.Cost.Structured.RenameFrame

/-! Run the checked header serializer in a fresh caller-selected tape bank.
The source ports remain fixed. Its cost includes the compiled call return,
and its frame retains all earlier payload and calibration tapes. -/
namespace Maxwell.Continuum.StoredHeader
open Maxwell.Cost Maxwell.Cost.Structured RationalAccumulator
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def relocatedCode (relocation : Equiv.Perm ℕ) (energyPort : ℕ) : Code :=
  .call ((code energyPort).compile.renameTapes relocation)

theorem relocated_executes (relocation : Equiv.Perm ℕ)
    (energyPort : ℕ) (energyLower : 733 ≤ energyPort)
    (fixed : ∀i∈emissionInputs energyPort,relocation i=i)
    (v : ℕ→ℕ) (B : ℕ) (hB : 34 ≤ B)
    (width : ∀i∈emissionInputs energyPort,(v i).bits.length ≤ B)
    (positive : ∀a∈fractions energyPort,0<prepared v a.2.2)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank (emissionInputs energyPort) v s.val)
    (fresh : ∀i∈emissionWork,Blank s.val (relocation i)) :
    ∃cost t,Executes input tape (relocatedCode relocation energyPort) cost s t ∧
      cost ≤ emissionCost B 0 0+1 ∧
      t.val.output=(bits energyPort v).reverse++s.val.output ∧
      t.val.address=s.val.address ∧t.val.memory=s.val.memory ∧
      t.val.inputHead=s.val.inputHead ∧t.val.randomCursor=s.val.randomCursor ∧
      (∀i,i∉emissionWork.image relocation→t.val.tapes i=s.val.tapes i) := by
  let a:=s.renameTapes relocation.symm
  have tapeEq (i : ℕ) : a.val.tapes i=s.val.tapes (relocation i) := rfl
  have blank (i : ℕ) (hi : i∈emissionWork) : Blank a.val i := by
    obtain ⟨origin,stored⟩:=fresh i hi
    exact ⟨origin,(tapeEq i).trans stored⟩
  have ba : NatAssign.Bank (emissionInputs energyPort) v a.val := by
    intro i hi
    exact word_of_eq ((tapeEq i).trans (congrArg s.val.tapes (fixed i hi))) (bank i hi)
  have za : NatAssign.Scratch a.val := by
    intro i hi
    apply blank i
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have header : WordCleanup.Bounded outputList 0 a.val := by
    intro i hi
    exact ⟨[],Nat.le_refl _,(zero_word_iff_blank _ _).mpr
      (blank i (Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))))⟩
  have canonical : WordCleanup.Bounded RationalCanonical.StoredEmission.words 0 a.val := by
    intro i hi
    exact ⟨[],Nat.le_refl _,(zero_word_iff_blank _ _).mpr
      (blank i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)))⟩
  obtain ⟨c,b,e,hc,out,_,address,memory,head,random,keep⟩:=executes energyPort energyLower
    v B 0 0 hB width positive input tape a ba za header canonical
  have run:=e.renamed_call relocation
  have back : a.renameTapes relocation=s:=Store.renameTapes_symm relocation s
  rw [back] at run
  refine ⟨c+1,b.renameTapes relocation,run,Nat.add_le_add_right hc 1,out,
    address,memory,head,random,?_⟩
  intro i hi
  have outside : relocation.symm i∉emissionWork := by
    intro member
    exact hi (Finset.mem_image.mpr ⟨relocation.symm i,member,relocation.apply_symm_apply i⟩)
  change b.val.tapes (relocation.symm i)=s.val.tapes i
  rw [keep _ outside,tapeEq,relocation.apply_symm_apply]

#print axioms relocated_executes
end Maxwell.Continuum.StoredHeader
