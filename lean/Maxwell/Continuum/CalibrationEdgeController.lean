import Maxwell.Cost.Structured.NatAssign.Values
import Maxwell.Cost.PhysicalMaterial.FixedSubtract

/-! Charged initialization and advancement of the certified edge tests.
The test count is read from the computed energy precision at port 4418. -/
namespace Maxwell.Continuum.Calibration.EdgeController
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word)
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def activeIds : Finset ℕ := {311}∪Finset.Icc 850 859
def ids : Finset ℕ := insert 4418 activeIds
def changed : Finset ℕ := {0,1,2,3,311}∪Finset.Icc 850 859

def initializePlan : List NatAssign.Instruction :=
  [.copy 4418 852,.literal 850 188,.literal 853 1,.literal 854 2,.literal 855 5,
    .literal 856 0,.literal 857 0,.literal 858 0,.literal 859 0,
    .copy 852 851,.multiply 854 851,.copy 850 311,.add 855 311]
def initializeCode : Code := NatAssign.code initializePlan
def initialValues (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values initializePlan v
def initializeCost (B : ℕ) : ℕ := 3000*8^initializePlan.length*(B+10)^2
def initialWidth (B : ℕ) : ℕ := 2^initializePlan.length*(B+9)

def advancePlan : List NatAssign.Instruction :=
  [.literal 853 1,.literal 855 5,.add 853 850,.copy 850 311,.add 855 311]
def advanceCode : Code := .seq (NatAssign.code advancePlan) (PhysicalMaterial.FixedSubtract.code 851 1)
def advancedValues (v : ℕ→ℕ) : ℕ→ℕ :=
  Function.update (NatAssign.values advancePlan v) 851 (v 851-1)
def advanceCost (B : ℕ) : ℕ := 3000*8^advancePlan.length*(B+5)^2+29*B+31
def advanceWidth (B : ℕ) : ℕ := 2^advancePlan.length*(B+4)

theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i := by
  simp only [ids,activeIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
  omega
theorem activeIds_ge (i : ℕ) (hi : i∈activeIds) : 4 ≤ i := ids_ge i (Finset.mem_insert_of_mem hi)
theorem initialize_valid : ∀a∈initializePlan,a.Valid ids := by
  simp [initializePlan,NatAssign.Instruction.Valid,ids,activeIds]
theorem advance_valid : ∀a∈advancePlan,a.Valid activeIds := by
  simp [advancePlan,NatAssign.Instruction.Valid,activeIds]

theorem initial_fields (v : ℕ→ℕ) :
    initialValues v 850=188 ∧ initialValues v 851=2*v 4418 ∧
    initialValues v 852=v 4418 ∧ initialValues v 311=193 ∧ initialValues v 4418=v 4418 := by
  simp [initialValues,initializePlan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem advanced_fields (v : ℕ→ℕ) :
    advancedValues v 850=v 850+1 ∧ advancedValues v 851=v 851-1 ∧
    advancedValues v 311=v 850+6 ∧ advancedValues v 4418=v 4418 := by
  simp [advancedValues,advancePlan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]
  omega

theorem initialize_executes (v : ℕ→ℕ) (B : ℕ)
    (width : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape initializeCode cost s t ∧ cost ≤ initializeCost B ∧
      NatAssign.Bank ids (initialValues v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(initialValues v i).bits.length ≤ initialWidth B) ∧
      Word t.val 850 188 ∧ Word t.val 851 (2*v 4418) ∧ Word t.val 311 193 ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨cost,t,execution,bound,bt,st,frame⟩ :=
    NatAssign.executes ids ids_ge initializePlan initialize_valid v input tape s bank scratch
  have literal : ∀a∈initializePlan,a.literalWidth≤B+8 := by
    simp [initializePlan,NatAssign.Instruction.literalWidth,
      show (188:ℕ).bits.length=8 by decide,show (2:ℕ).bits.length=2 by decide,
      show (5:ℕ).bits.length=3 by decide]
  have inputWidth : ∀i∈ids,(v i).bits.length≤B+8 := fun i hi=>(width i hi).trans (by omega)
  have outputWidth := NatAssign.values_width ids initializePlan initialize_valid v (B+8) inputWidth literal
  change NatAssign.Bank ids (initialValues v) t.val at bt
  have fields:=initial_fields v
  refine ⟨cost,t,execution,bound.trans (NatAssign.price_bound ids initializePlan initialize_valid v
    (B+8) inputWidth literal),bt,st,?_,?_,?_,?_,frame.mono (by decide)⟩
  · intro i hi
    exact (Nat.le_add_right _ 1).trans (outputWidth i hi)
  · simpa only [fields.1] using bt 850 (by decide)
  · simpa only [fields.2.1] using bt 851 (by decide)
  · simpa only [fields.2.2.2.1] using bt 311 (by decide)

theorem advance_executes (v : ℕ→ℕ) (B : ℕ) (positive : 0<v 851)
    (width : ∀i∈activeIds,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank activeIds v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape advanceCode cost s t ∧ cost≤advanceCost B ∧
      NatAssign.Bank activeIds (advancedValues v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈activeIds,(advancedValues v i).bits.length≤advanceWidth B) ∧
      Word t.val 850 (v 850+1) ∧ Word t.val 851 (v 851-1) ∧ Word t.val 311 (v 850+6) ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,h0,bu,su,f0⟩ :=
    NatAssign.executes activeIds activeIds_ge advancePlan advance_valid v input tape s bank scratch
  have count : NatAssign.values advancePlan v 851=v 851 := by
    exact NatAssign.values_preserves advancePlan v 851 (by decide)
  have oldCount : Word u.val 851 (v 851) := by simpa only [count] using bu 851 (by decide)
  obtain ⟨c1,t,e1,h1,word,f1⟩ := PhysicalMaterial.FixedSubtract.executes 851 1 (v 851)
    positive input tape u oldCount
  have literal : ∀a∈advancePlan,a.literalWidth≤B+3 := by
    simp [advancePlan,NatAssign.Instruction.literalWidth,show (5:ℕ).bits.length=3 by decide]
  have inputWidth : ∀i∈activeIds,(v i).bits.length≤B+3 := fun i hi=>(width i hi).trans (by omega)
  have h0' := h0.trans (NatAssign.price_bound activeIds advancePlan advance_valid v (B+3) inputWidth literal)
  have bt : NatAssign.Bank activeIds (advancedValues v) t.val := by
    intro i hi
    by_cases same : i=851
    · subst i;simpa only [advancedValues,Function.update_self] using word
    · simpa only [advancedValues,Function.update_of_ne same] using
        RationalAccumulator.word_of_eq (f1.tapes i (by simpa using same)) (bu i hi)
  have fields:=advanced_fields v
  refine ⟨c0+c1,t,e0.seq e1,?_,bt,?_,?_,?_,?_,?_,
    (f0.mono (by decide)).trans (f1.mono (by decide))⟩
  · have countWidth:=width 851 (by decide)
    unfold PhysicalMaterial.FixedSubtract.costBound at h1
    norm_num only [Nat.add_assoc] at h0'
    unfold advanceCost
    omega
  · intro i hi
    exact RationalAccumulator.blank_of_eq (f1.tapes i (by simp;omega)) (su i hi)
  · intro i hi
    by_cases same : i=851
    · subst i
      simp only [advancedValues,Function.update_self]
      have smaller:=Nat.size_le_size (Nat.sub_le (v 851) 1)
      rw [←Nat.size_eq_bits_len,←Nat.size_eq_bits_len] at smaller
      have old:=width 851 (by decide)
      unfold advanceWidth advancePlan
      simp only [List.length_cons,List.length_nil] at *
      omega
    · simp only [advancedValues,Function.update_of_ne same]
      exact (Nat.le_add_right _ 1).trans
        (NatAssign.values_width activeIds advancePlan advance_valid v (B+3) inputWidth literal i hi)
  · simpa only [fields.1] using bt 850 (by decide)
  · simpa only [fields.2.1] using bt 851 (by decide)
  · simpa only [fields.2.2.1] using bt 311 (by decide)

#print axioms initialize_executes
#print axioms advance_executes
end Maxwell.Continuum.Calibration.EdgeController
