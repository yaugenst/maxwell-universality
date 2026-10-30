import Maxwell.Continuum.CalibrationRootGridFinish

/-! Fixed startup computes the grid cube and initializes the two sums.
The stored counter and normalization denominator are actual outputs. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def clockIds : Finset ℕ := {331,342,343,344}
def clockSetup : List NatAssign.Instruction :=
  [.copy 331 343,.multiply 331 343,.multiply 331 343,.literal 344 1,.copy 343 342]
def clockValues (n : ℕ→ℕ) : ℕ→ℕ := NatAssign.values clockSetup n
def clockWorkspace : Finset ℕ := {0,1,2,3}∪clockIds

def zeroSums : Control := Control.prepend [.literal 10 0,.literal 11 0] .done
def zeroValues (v : ℕ→Parts) : ℕ→Parts := zeroSums.evaluate v
def startCode : Code := .seq (NatAssign.code clockSetup) zeroSums.code
def startWorkspace (S : Finset ℕ) : Finset ℕ := clockWorkspace∪RationalDataflow.workspace S

theorem clockSetup_valid : ∀a∈clockSetup,a.Valid clockIds := by
  simp [clockSetup,NatAssign.Instruction.Valid,clockIds]

theorem clockValues_result (n : ℕ→ℕ) :
    clockValues n 331=n 331 ∧ clockValues n 342=(n 331)^3 ∧
      clockValues n 343=(n 331)^3 ∧ clockValues n 344=1 := by
  simp [clockValues,clockSetup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]
  ring

theorem zeroSums_valid (S : Finset ℕ) (hS : sumInputs⊆S) : zeroSums.Valid S := by
  have h10 := hS (show 10∈sumInputs by decide)
  have h11 := hS (show 11∈sumInputs by decide)
  simp [zeroSums,Control.prepend,Control.Valid,Instruction.Valid,h10,h11]

theorem zeroSums_admissible (v : ℕ→Parts) : zeroSums.AdmissibleTrace v := by
  simp [zeroSums,Control.prepend,Control.AdmissibleTrace,Instruction.Admissible]

theorem zeroValues_zero (v : ℕ→Parts) : (zeroValues v 10).value=0 ∧ (zeroValues v 11).value=0 := by
  simp [zeroValues,zeroSums,Control.prepend,Control.evaluate,Instruction.update,Parts.literal_value]

theorem zeroValues_other (v : ℕ→Parts) (i : ℕ) (hi : i≠10 ∧ i≠11) : zeroValues v i=v i := by
  simp [zeroValues,zeroSums,Control.prepend,Control.evaluate,Instruction.update,hi.1,hi.2]

theorem zeroSums_widthTrace (S : Finset ℕ) (v : ℕ→Parts) (I : ℕ) (hI : 1≤I)
    (hw : WidthBank S I v) : zeroSums.WidthTrace S I v := by
  have hz : (Parts.literal 0).Width I :=
    (show (Parts.literal 0).Width 1 by change 0≤1 ∧ 0≤1 ∧ 1≤1;omega).mono hI
  exact ⟨hw,hz,hw.update 10 hz,hz,(hw.update 10 hz).update 11 hz⟩

theorem clock_outside_rational (S : Finset ℕ) (i : ℕ) (hi : i∈clockIds) :
    i∉RationalDataflow.workspace S := by
  apply FractionWord.outside
  simp only [clockIds,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem rationalReady_clock {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : Ready S v s) (f : BinaryPrecision.Frame clockWorkspace s.val t.val)
    (hz : NatAssign.Scratch t.val) : Ready S v t := by
  refine ⟨?_,hz⟩
  intro i hi
  have hge := ids_ge_ten S i hi
  have hout : i∉clockWorkspace := by
    intro hm
    rcases Finset.mem_union.mp hm with hm|hm
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      omega
    · exact clock_outside_rational S i hm (Finset.mem_union_right _ hi)
  exact word_of_eq (f.tapes i hout) (h.1 i hi)

theorem glueClean_clock {s t : Store} (h : Glue.Clean s.val)
    (f : BinaryPrecision.Frame clockWorkspace s.val t.val) : Glue.Clean t.val := by
  intro i hi
  have hm := Finset.mem_of_mem_erase hi
  have hge := GlueMachine.Runtime.ids_ge i hm
  have hout : i∉clockWorkspace := by
    intro hx
    rcases Finset.mem_union.mp hx with hx|hx
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      omega
    · exact Finset.disjoint_left.mp (show Disjoint clockIds GlueMachine.Runtime.ids by decide) hx hm
  exact blank_of_eq (f.tapes i hout) (h i hi)

theorem phaseClean_clock {s t : Store} (h : Phase.Runtime.Clean s.val)
    (f : BinaryPrecision.Frame clockWorkspace s.val t.val) : Phase.Runtime.Clean t.val := by
  intro i hi
  have hm := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
  have hge := PhaseMachine.Runtime.ids_ge i hm
  have hout : i∉clockWorkspace := by
    intro hx
    rcases Finset.mem_union.mp hx with hx|hx
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      omega
    · exact Finset.disjoint_left.mp (show Disjoint clockIds PhaseMachine.Runtime.ids by decide) hx hm
  exact blank_of_eq (f.tapes i hout) (h i hi)

theorem clock_executes (n : ℕ→ℕ) (B : ℕ) (hB : 1≤B)
    (hw : ∀i∈clockIds,(n i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hb : NatAssign.Bank clockIds n s.val)
    (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (NatAssign.code clockSetup) cost s t ∧ cost≤stageCost B ∧
      NatAssign.Bank clockIds (clockValues n) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame clockWorkspace s.val t.val := by
  apply fixedBankStage_executes clockIds _ clockSetup clockSetup_valid (by decide) n B hw _ input tape s hb hz
  · intro i hi
    simp only [clockIds,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  · simp [clockSetup,NatAssign.Instruction.literalWidth,hB]

#print axioms clock_executes
end Maxwell.Continuum.RationalDataflow.RootGrid
