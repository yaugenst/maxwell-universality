import Maxwell.Continuum.CalibrationEdgeScalarMachine
import Maxwell.Cost.Structured.TapeBlockSwapFrame

/-! The edge scalar evaluator keeps its reusable Machin bank at900..923,
beside the basis-column workspace and the persistent bracket. -/
namespace Maxwell.Continuum.Calibration.EdgeScalar
open Maxwell.Cost Maxwell.Cost.Structured RationalAccumulator RationalDataflow
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

def relocation : Equiv.Perm ℕ := TapeBlockSwap.permutation 610 24 290 (by decide)
def code : Code := .call (coreCode.compile.renameTapes relocation)
def cost (N B : ℕ) : ℕ := coreCost N B+1
def work : Finset ℕ := coreWork.image relocation
def RelocatedFresh (s : BitRAMState) : Prop := ∀i,900≤ i→i<924→Blank s i

theorem relocation_involutive (i : ℕ) : relocation (relocation i)=i :=
  TapeBlockSwap.involutive 610 24 290 (by decide) i

theorem state_tape (s : Store) (i : ℕ) :
    (s.renameTapes relocation).val.tapes i=s.val.tapes (relocation i) := by
  simp only [Store.renameTapes,BitRAMState.renameTapes,Function.comp_apply,relocation,TapeBlockSwap.symm]

theorem twice (s : Store) : (s.renameTapes relocation).renameTapes relocation=s :=
  Store.renameTapes_symm relocation s

theorem moved (i : ℕ) (lo : 610≤ i) (hi : i<634) : relocation i=i+290 :=
  TapeBlockSwap.apply_inside 610 24 290 _ i lo hi

theorem fixed_large (i : ℕ) (hi : 1000≤ i) : relocation i=i :=
  TapeBlockSwap.apply_outside 610 24 290 _ i (Or.inr (by omega)) (Or.inr (by omega))

theorem fixed_small (i : ℕ) (hi : i<4) : relocation i=i :=
  TapeBlockSwap.apply_outside 610 24 290 _ i (Or.inl (by omega)) (Or.inl (by omega))

theorem executes (N B : ℕ) (p : Parts) (old : ℕ→Parts)
    (midWidth : p.Width B) (oldWidth : WidthBank saved B old)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (precision : Word s.val 850 N) (fresh : RelocatedFresh s.val) (scratch : NatAssign.Scratch s.val)
    (previous : Cells saved old s.val) (midpoint : StoredParts.Stored (positivePort 2302) p s.val) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost N B ∧
      Cells saved (result N p) t.val ∧ WidthBank saved (resultWidth N B) (result N p) ∧
      NatAssign.Scratch t.val ∧ RelocatedFresh t.val ∧ BinaryPrecision.Frame work s.val t.val := by
  have large (i : ℕ) (hi : 1000≤ i) : (s.renameTapes relocation).val.tapes i=s.val.tapes i := by
    rw [state_tape,fixed_large i hi]
  have prec : Word (s.renameTapes relocation).val 850 N :=
    word_of_eq ((state_tape s 850).trans (congrArg s.val.tapes (by decide : relocation 850=850))) precision
  have clear : Fresh (s.renameTapes relocation).val := by
    intro i hi
    have range:=(machine_member i).mp hi
    obtain ⟨origin,word⟩:=fresh (i+290) (by omega) (by omega)
    exact ⟨origin,((state_tape s i).trans (congrArg s.val.tapes (moved i range.1 range.2))).trans word⟩
  have low : NatAssign.Scratch (s.renameTapes relocation).val := by
    intro i hi
    exact blank_of_eq ((state_tape s i).trans (congrArg s.val.tapes (fixed_small i hi))) (scratch i hi)
  obtain ⟨c,a,e,charge,stored,width,blank,empty,frame⟩:=core_executes N B p old midWidth oldWidth input tape
    (s.renameTapes relocation) prec clear low (previous.transfer large)
    ⟨word_of_eq (large _ (by decide)) midpoint.1,
     word_of_eq (large _ (by decide)) midpoint.2.1,word_of_eq (large _ (by decide)) midpoint.2.2⟩
  refine ⟨c+1,a.renameTapes relocation,?_,Nat.add_le_add_right charge 1,?_,width,?_,?_,?_⟩
  · simpa only [code,twice] using e.renamed_call relocation
  · apply stored.transfer
    intro i hi
    rw [state_tape,fixed_large i hi]
  · intro i hi
    exact blank_of_eq ((state_tape a i).trans (congrArg a.val.tapes (fixed_small i hi))) (blank i hi)
  · intro i lo hi
    have range : 610≤ i-290 ∧ i-290<634 := by omega
    have forward : relocation (i-290)=i := by rw [moved _ range.1 range.2];omega
    have backward : relocation i=i-290 := by
      exact (congrArg relocation forward.symm).trans (relocation_involutive (i-290))
    obtain ⟨origin,word⟩:=empty (i-290) ((machine_member _).mpr range)
    exact ⟨origin,((state_tape a i).trans (congrArg a.val.tapes backward)).trans word⟩
  · have renamed:=frame.renameTapes relocation
    have equality:=congrArg Subtype.val (twice s)
    exact equality ▸ renamed

theorem work_range (i : ℕ) (hi : i∈work) :
    i<4 ∨ (900≤ i ∧ i<924) ∨ (1696≤ i ∧ i≤1710) := by
  obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hi
  rcases Finset.mem_union.mp hj with lowOrMachine|output
  · rcases Finset.mem_union.mp lowOrMachine with low|machine
    · have bound : j<4 := by simp only [Finset.mem_insert,Finset.mem_singleton] at low;omega
      rw [fixed_small j bound]
      exact Or.inl bound
    · have range:=(machine_member j).mp machine
      rw [moved j range.1 range.2]
      exact Or.inr (Or.inl (by omega))
  · have range:=output_range j output
    rw [fixed_large j (by omega)]
    exact Or.inr (Or.inr range)

#print axioms executes
end Maxwell.Continuum.Calibration.EdgeScalar
