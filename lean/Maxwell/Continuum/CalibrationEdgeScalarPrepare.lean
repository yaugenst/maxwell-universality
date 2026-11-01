import Maxwell.Continuum.CalibrationEdgeScalarPlan
import Maxwell.Cost.Structured.WordCleanup

/-! Read the current edge-test precision and execute the Machin evaluator.
The six-bit convention inside piCenter is included in the actual addition. -/
namespace Maxwell.Continuum.Calibration.EdgeScalar
open Maxwell.Cost Maxwell.Cost.Structured RationalAccumulator RationalDataflow
set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

def machineTapes : List ℕ := List.range' 610 24
def machineSet : Finset ℕ := machineTapes.toFinset
def Fresh (s : BitRAMState) : Prop := ∀i∈machineSet,Blank s i
def prepareIds : Finset ℕ := {629,630,850}
def preparePlan : List NatAssign.Instruction :=
  [.copy 850 630,.literal 629 7,.add 629 630,.literal 629 0]
def initialValues (N : ℕ) (i : ℕ) : ℕ := if i=850 then N else 0
def prepareCode : Code := NatAssign.code preparePlan
def machinCode : Code := .seq prepareCode Machin.Runtime.program
def prepareCost (N : ℕ) : ℕ := 3000*8^4*(N+9)^2
def machinCost (N : ℕ) : ℕ := prepareCost N+Machin.Runtime.costBound (N+7)
def cleanupWidth (N : ℕ) : ℕ := Machin.finalWidth (N+7)+N+7

theorem machine_member (i : ℕ) : i∈machineSet ↔ 610≤ i ∧ i<634 := by
  simp only [machineSet,machineTapes,List.mem_toFinset,List.mem_range'_1]

theorem prepare_valid : ∀a∈preparePlan,a.Valid prepareIds := by
  simp [preparePlan,prepareIds,NatAssign.Instruction.Valid]

theorem prepare_executes (N : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (precision : Word s.val 850 N) (fresh : Fresh s.val) (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape prepareCode steps s t ∧ steps≤prepareCost N ∧
      Word t.val 630 (N+7) ∧ Blank t.val 629 ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame ({0,1,2,3,629,630}:Finset ℕ) s.val t.val := by
  have bank : NatAssign.Bank prepareIds (initialValues N) s.val := by
    intro i hi
    simp only [prepareIds,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · simpa [initialValues,zero_word_iff_blank] using fresh 629 (by decide)
    · simpa [initialValues,zero_word_iff_blank] using fresh 630 (by decide)
    · simpa [initialValues] using precision
  obtain ⟨c,t,e,charge,stored,blank,frame⟩:=NatAssign.executes prepareIds (by
    simp only [prepareIds,Finset.mem_insert,Finset.mem_singleton];omega)
    preparePlan prepare_valid (initialValues N) input tape s bank scratch
  have width : ∀i∈prepareIds,(initialValues N i).bits.length≤N+7 := by
    intro i _
    unfold initialValues
    split_ifs
    · exact (Machin.Runtime.nat_bits_le_self N).trans (by omega)
    · simp
  have literals : ∀a∈preparePlan,a.literalWidth≤N+7 := by
    simp [preparePlan,NatAssign.Instruction.literalWidth]
    change 3≤N+7
    omega
  have cost:=NatAssign.price_bound prepareIds preparePlan prepare_valid (initialValues N) (N+7) width literals
  have value : NatAssign.values preparePlan (initialValues N) 630=N+7 ∧
      NatAssign.values preparePlan (initialValues N) 629=0 := by
    simp [preparePlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,initialValues,Nat.add_comm]
  refine ⟨c,t,e,charge.trans cost,value.1 ▸ stored 630 (by decide),?_,blank,frame.mono (by decide)⟩
  simpa only [value.2,zero_word_iff_blank] using stored 629 (by decide)

theorem machin_executes (N : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (precision : Word s.val 850 N) (fresh : Fresh s.val) (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape machinCode steps s t ∧ steps≤machinCost N ∧
      NatAssign.Bank Machin.allIds (Machin.finalValues (N+7)) t.val ∧ NatAssign.Scratch t.val ∧
      Machin.Runtime.InputReady (N+7) t.val ∧ Blank t.val 629 ∧
      BinaryPrecision.Frame ({0,1,2,3}∪machineSet) s.val t.val := by
  obtain ⟨c,a,e,charge,word,zero,blank,frame⟩:=prepare_executes N input tape s precision fresh scratch
  have initial : NatAssign.Bank Machin.allIds (fun _=>0) a.val := by
    intro i hi
    have lo : 610≤ i ∧ i≤627 := by
      simp only [Machin.allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    rw [zero_word_iff_blank]
    exact blank_of_eq (frame.tapes i (by
      simp only [Finset.mem_insert,Finset.mem_singleton];omega)) (fresh i ((machine_member i).mpr (by omega)))
  have keep (i : ℕ) (hi : i∈({619,628,631,632,633}:Finset ℕ)) : Blank a.val i := by
    have range : 610≤ i ∧ i<634 := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega
    have outside : i∉({0,1,2,3,629,630}:Finset ℕ) := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi ⊢;omega
    exact blank_of_eq (frame.tapes i outside) (fresh i ((machine_member i).mpr range))
  obtain ⟨d,t,et,dt,stored,clear,aux,ft⟩:=Machin.Runtime.program_executes (N+7) input tape a initial blank
    ⟨word,keep 619 (by decide),keep 628 (by decide),keep 631 (by decide),keep 632 (by decide),keep 633 (by decide)⟩
  refine ⟨c+d,t,e.seq et,Nat.add_le_add charge dt,stored,clear,aux,
    blank_of_eq (ft.tapes 629 (by decide)) zero,(frame.mono (by decide)).trans (ft.mono (by decide))⟩

theorem machin_bounded (N : ℕ) (s : BitRAMState)
    (bank : NatAssign.Bank Machin.allIds (Machin.finalValues (N+7)) s)
    (aux : Machin.Runtime.InputReady (N+7) s) (zero : Blank s 629) :
    WordCleanup.Bounded machineTapes (cleanupWidth N) s := by
  intro i hi
  have range : 610≤ i ∧ i<634 := (machine_member i).mp (by simpa only [machineSet,List.mem_toFinset] using hi)
  by_cases member : i∈Machin.allIds
  · exact ⟨(Machin.finalValues (N+7) i).bits,(Machin.finalValues_width _ i member).trans
      (by unfold cleanupWidth;omega),bank i member⟩
  · have cases : i=619 ∨ i=628 ∨ i=629 ∨ i=630 ∨ i=631 ∨ i=632 ∨ i=633 := by
      simp only [Machin.allIds,RationalArctan.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at member
      omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr aux.index⟩
    · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr aux.two⟩
    · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr zero⟩
    · exact ⟨(N+7).bits,(Machin.Runtime.nat_bits_le_self _).trans (by unfold cleanupWidth;omega),aux.precision⟩
    · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr aux.terms⟩
    · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr aux.count⟩
    · exact ⟨[],Nat.zero_le _,(zero_word_iff_blank _ _).mpr aux.six⟩

#print axioms machin_executes
#print axioms machin_bounded
end Maxwell.Continuum.Calibration.EdgeScalar
