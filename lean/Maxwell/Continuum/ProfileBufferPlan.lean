import Maxwell.Continuum.ProfileProducerBounds
import Maxwell.Continuum.CalibrationWidthClock
import Maxwell.Continuum.CalibrationNeumannLayout

/-! Fixed natural arithmetic allocates both coefficient buffers from the
requested precision and a heap pointer. Initial memory contents are arbitrary. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

def bufferIds : Finset ℕ := {660,661,704,705,706,707,708,709}
def bufferHeaderIds : Finset ℕ := {200,202,203,204,210,212,213,214}
def allocationIds : Finset ℕ := bufferIds∪bufferHeaderIds
def bufferInput (N D heap i : ℕ) : ℕ :=
  if i=660 then N else if i=661 then D else if i=705 then heap else 0

def bufferBudgetPlan : List NatAssign.Instruction :=
  [.copy 660 704,.literal 706 1,.add 706 704,.copy 704 707,.multiply 707 704,
   .literal 706 (2^46),.multiply 706 704,.literal 706 1,.add 706 704,
   .copy 704 708,.multiply 704 708,.copy 708 704,
   .copy 704 707,.multiply 707 704,.copy 704 707,.multiply 707 704,
   .copy 704 707,.multiply 707 704,.multiply 708 704,
   .literal 706 (2^500),.multiply 706 704,.literal 706 0,.literal 707 0,.literal 708 0]
def bufferWidthPlan : List NatAssign.Instruction :=
  [.copy 704 708,.literal 706 16,.multiply 706 708,.copy 661 709,
   .literal 706 96,.multiply 706 709,.add 709 708,.literal 706 112,
   .add 706 708,.literal 706 0,.literal 709 0]
def bufferAddressPlan : List NatAssign.Instruction :=
  [.copy 704 210,.copy 705 212,.copy 661 706,.multiply 704 706,
   .copy 212 213,.add 706 213,.copy 213 214,.add 706 214,.copy 214 202,.add 706 202,
   .copy 708 200,.copy 661 706,.multiply 708 706,.copy 202 203,.add 706 203,
   .copy 203 204,.add 706 204,.copy 204 709,.add 706 709,.literal 706 0]

def bufferBudgetValues (N D heap : ℕ) : ℕ→ℕ := NatAssign.values bufferBudgetPlan (bufferInput N D heap)
def bufferWidthValues (N D heap : ℕ) : ℕ→ℕ := NatAssign.values bufferWidthPlan (bufferBudgetValues N D heap)
def bufferAddressValues (N D heap : ℕ) : ℕ→ℕ := NatAssign.values bufferAddressPlan (bufferWidthValues N D heap)
def bufferWidth (N D : ℕ) : ℕ := encodedTableWidth D (runtimeBudget N)
def secondBufferBase (N D heap : ℕ) : ℕ := heap+3*D*runtimeBudget N
def bufferHeapEnd (N D heap : ℕ) : ℕ := secondBufferBase N D heap+3*D*bufferWidth N D

theorem bufferBudgetPlan_valid : ∀a∈bufferBudgetPlan,a.Valid allocationIds := by
  simp [bufferBudgetPlan,NatAssign.Instruction.Valid,allocationIds,bufferIds]
theorem bufferWidthPlan_valid : ∀a∈bufferWidthPlan,a.Valid allocationIds := by
  simp [bufferWidthPlan,NatAssign.Instruction.Valid,allocationIds,bufferIds]
theorem bufferAddressPlan_valid : ∀a∈bufferAddressPlan,a.Valid allocationIds := by
  simp [bufferAddressPlan,NatAssign.Instruction.Valid,allocationIds,bufferIds,bufferHeaderIds]

theorem bufferBudgetValues_eq (N D heap i : ℕ) : bufferBudgetValues N D heap i=
    if i=704 then runtimeBudget N else bufferInput N D heap i := by
  by_cases h : i=704
  · subst i
    simp only [bufferBudgetValues,bufferBudgetPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update_self,
      Function.update_of_ne (by decide : (704:ℕ)≠706),
      Function.update_of_ne (by decide : (704:ℕ)≠707),
      Function.update_of_ne (by decide : (704:ℕ)≠708)]
    simp [bufferInput,runtimeBudget,workingBudget,producerSize,pow_two]
    ring
  by_cases h6 : i=706
  · subst i
    simp [bufferBudgetValues,bufferBudgetPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,bufferInput]
  by_cases h7 : i=707
  · subst i
    simp [bufferBudgetValues,bufferBudgetPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,bufferInput]
  by_cases h8 : i=708
  · subst i
    simp [bufferBudgetValues,bufferBudgetPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,bufferInput]
  rw [ite_eq_right h]
  exact values_unchanged bufferBudgetPlan _ i (by
    simp [bufferBudgetPlan,NatAssign.Instruction.target,Ne.symm h,Ne.symm h6,Ne.symm h7,Ne.symm h8])

theorem bufferWidthValues_eq (N D heap i : ℕ) : bufferWidthValues N D heap i=
    if i=708 then bufferWidth N D else bufferBudgetValues N D heap i := by
  by_cases h : i=708
  · subst i
    simp [bufferWidthValues,bufferWidthPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,bufferBudgetValues_eq,bufferInput,
      bufferWidth,encodedTableWidth,correctionWorkingWidth,endpointWorkingWidth]
    omega
  by_cases h6 : i=706
  · subst i
    simp [bufferWidthValues,bufferWidthPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,bufferBudgetValues_eq,bufferInput]
  by_cases h9 : i=709
  · subst i
    simp [bufferWidthValues,bufferWidthPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,bufferBudgetValues_eq,bufferInput]
  rw [ite_eq_right h]
  exact values_unchanged bufferWidthPlan _ i (by
    simp [bufferWidthPlan,NatAssign.Instruction.target,Ne.symm h,Ne.symm h6,Ne.symm h9])

def memoryTable (n width heap : ℕ) (hw : 0<width) (memory : ℕ→Bool) : PartArray.Table n where
  width := width.bits
  basePositive := heap.bits
  baseNegative := (heap+n*width).bits
  baseDenominator := (heap+2*n*width).bits
  clock := List.replicate width false
  positive := Calibration.NeumannMachine.memoryWords memory heap width n
  negative := Calibration.NeumannMachine.memoryWords memory (heap+n*width) width n
  denominator := Calibration.NeumannMachine.memoryWords memory (heap+2*n*width) width n
  width_pos := by rw [Nat.size_eq_bits_len];exact Nat.size_pos.mpr hw
  clock_length := by simp only [List.length_replicate,addressValue_bits]

#print axioms bufferBudgetValues_eq
#print axioms bufferWidthValues_eq
end Maxwell.Continuum.Profile.Runtime
