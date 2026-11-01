import Maxwell.Continuum.RationalDataflowProgram
import Maxwell.Cost.Structured.NatAssign.Values

/-! Initialize a finite rational register bank by charged literal writes.
The register set stays symbolic, including for generated matrix circuits. -/
namespace Maxwell.Continuum.RationalDataflow.Initialize
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)

def parts : ℕ→Parts := fun _=>Parts.literal 0
def plan (S : Finset ℕ) : List NatAssign.Instruction :=
  ((ids S).sort (·≤·)).map (fun i=>.literal i (dataValues parts i))
def code (S : Finset ℕ) : Code := NatAssign.code (plan S)
def cost (S : Finset ℕ) : ℕ := 3000*8^(ids S).card*3^2

theorem valid (S : Finset ℕ) : ∀a∈plan S,a.Valid (ids S) := by
  intro a ha
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
  simpa only [Finset.mem_sort,NatAssign.Instruction.Valid] using hi

theorem good (S : Finset ℕ) : Good S parts := fun _ _=>Parts.literal_valid 0

theorem width (S : Finset ℕ) : WidthBank S 1 parts := by
  intro i _
  change (Parts.literal 0).Width 1
  norm_num [Parts.Width,Parts.literal]

theorem words_width (S : Finset ℕ) : ∀i∈ids S,(dataValues parts i).bits.length≤1 :=
  dataValues_width S parts 1 (width S)

def resetCost (S : Finset ℕ) (B : ℕ) : ℕ := 3000*8^(ids S).card*(B+2)^2

theorem stored_executes (S : Finset ℕ) (n : ℕ→ℕ) (B : ℕ) (hB : 1≤ B)
    (width : ∀i∈ids S,(n i).bits.length≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank (ids S) n s.val) (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape (code S) steps s t ∧ steps≤ resetCost S B ∧
      Ready S parts t ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨steps,t,execution,charge,output,clear,frame⟩:=
    NatAssign.executes (ids S) (ids_ge S) (plan S) (valid S) n input tape s bank scratch
  refine ⟨steps,t,execution,?_,⟨?_,clear⟩,frame.mono ?_⟩
  · apply charge.trans
    have h:=NatAssign.price_bound (ids S) (plan S) (valid S) n B width
      (by
        intro a ha
        obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
        exact (words_width S i (by simpa only [Finset.mem_sort] using hi)).trans hB)
    simpa only [plan,List.length_map,Finset.length_sort,resetCost] using h
  · intro i hi
    have h:=output i hi
    simpa only [plan,NatAssign.values_literals,Finset.mem_sort,ite_eq_left hi] using h
  · intro i hi
    rcases Finset.mem_union.mp hi with low | assigned
    · exact Finset.mem_union_left _ low
    · obtain ⟨a,ha,target⟩:=List.mem_map.mp (List.mem_toFinset.mp assigned)
      obtain ⟨j,hj,rfl⟩:=List.mem_map.mp ha
      exact Finset.mem_union_right _ (target ▸ (by
        simpa only [Finset.mem_sort,NatAssign.Instruction.target] using hj))

theorem executes (S : Finset ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (fresh : ∀i∈ids S,Blank s.val i) (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape (code S) steps s t ∧ steps≤ cost S ∧
      Ready S parts t ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  exact stored_executes S (fun _=>0) 1 (by decide) (by simp) input tape s
    (fun i hi=>(RationalAccumulator.zero_word_iff_blank _ _).mpr (fresh i hi)) scratch

theorem reset_executes (S : Finset ℕ) (v : ℕ→Parts) (B : ℕ) (hB : 1≤ B)
    (width : WidthBank S B v) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (ready : Ready S v s) :
    ∃steps t,Executes input tape (code S) steps s t ∧ steps≤ resetCost S B ∧
      Ready S parts t ∧ BinaryPrecision.Frame (workspace S) s.val t.val :=
  stored_executes S (dataValues v) B hB (dataValues_width S v B width)
    input tape s ready.1 ready.2

#print axioms executes
#print axioms reset_executes
end Maxwell.Continuum.RationalDataflow.Initialize
