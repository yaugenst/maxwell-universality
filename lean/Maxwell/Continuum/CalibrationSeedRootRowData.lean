import Maxwell.Continuum.CalibrationSeedRootMeaning
import Maxwell.Continuum.CalibrationArrayDecodeLoad

/-! Runtime decoding for one alias row. Six fixed output producers share
these coordinates; no polarization or real/imaginary dispatcher is needed. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

def rowIds : Finset ℕ := ids∪ArrayDecodeMachine.ports∪NaturalQuotient.workPorts
def rowWorkspace : Finset ℕ := {0,1,2,3,4}∪rowIds
def rowPrepare : List NatAssign.Instruction :=
  [.literal 782 2,.literal 783 3,.copy 750 311,.multiply 783 311,.add 751 311,
   .copy 780 310,.multiply 783 310,.literal 220 0,.literal 221 0,.literal 222 0,.literal 223 0]
def rowPrepared (v : ℕ→ℕ) := NatAssign.values rowPrepare v
def rowHalved (v : ℕ→ℕ) := ArrayDecodeMachine.divModValues (rowPrepared v) 750 782 752 784
def rowFinish : List NatAssign.Instruction := [.copy 317 753,.copy 319 754,.copy 320 755]
def rowValues (v : ℕ→ℕ) := NatAssign.values rowFinish (ArrayDecodeMachine.output (rowHalved v))

theorem rowIds_lower (i : ℕ) (hi : i∈rowIds) : 10 ≤ i := by
  simp only [rowIds,ids,extra,SelectedParameters.Compare.ids,ArrayDecodeMachine.ports,
    NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
  omega
theorem rowPrepare_valid : ∀a∈rowPrepare,a.Valid rowIds := by
  simp [rowPrepare,NatAssign.Instruction.Valid,rowIds,ids,extra,SelectedParameters.Compare.ids,
    ArrayDecodeMachine.ports,NaturalQuotient.workPorts]
theorem rowFinish_valid : ∀a∈rowFinish,a.Valid rowIds := by
  simp [rowFinish,NatAssign.Instruction.Valid,rowIds,ids,extra,SelectedParameters.Compare.ids,
    ArrayDecodeMachine.ports]

theorem rowPrepared_fields (v : ℕ→ℕ) :
    rowPrepared v 750=v 750 ∧ rowPrepared v 782=2 ∧
    rowPrepared v 311=3*v 750+v 751 ∧ rowPrepared v 310=3*v 780 ∧
    (∀i∈NaturalQuotient.workPorts,rowPrepared v i=0) := by
  simp [rowPrepared,rowPrepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,NaturalQuotient.workPorts,Nat.add_comm]
theorem rowHalved_fields (v : ℕ→ℕ) :
    rowHalved v 752=v 750/2 ∧ rowHalved v 311=3*v 750+v 751 ∧ rowHalved v 310=3*v 780 ∧
    (∀i∈NaturalQuotient.workPorts,rowHalved v i=0) := by
  have h := rowPrepared_fields v
  simp [rowHalved,ArrayDecodeMachine.divModValues,h.1,h.2.1,h.2.2.1,h.2.2.2.1,
    NaturalQuotient.workPorts,h.2.2.2.2 220 (by decide),h.2.2.2.2 221 (by decide),
    h.2.2.2.2 222 (by decide),h.2.2.2.2 223 (by decide)]

theorem rowValues_coordinates (v : ℕ→ℕ) :
    coordinates (rowValues v)=decodedCoordinates (3*v 750+v 751) (3*v 780) := by
  have ho := ArrayDecodeMachine.output_coordinates (rowHalved v)
  have fields := rowHalved_fields v
  funext j
  have hj := ho j
  rw [fields.2.1,fields.2.2.1] at hj
  convert hj using 1
  fin_cases j <;> simp [coordinates,rowValues,rowFinish,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem rowValues_half (v : ℕ→ℕ) : rowValues v 752=v 750/2 := by
  rw [rowValues,NatAssign.values_preserves rowFinish _ 752 (by decide),
    ArrayDecodeMachine.output_outside _ _ (by decide)]
  exact (rowHalved_fields v).1

theorem rowValues_keep (v : ℕ→ℕ) (i : ℕ)
    (hi : i∈({750,751,780}:Finset ℕ) ∨ i∈RationalMagnitude.ids ∨ i∈NaturalQuotient.workPorts) :
    rowValues v i=if i∈NaturalQuotient.workPorts then 0 else v i := by
  have bounds := hi
  simp only [RationalMagnitude.ids,NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at bounds
  rw [rowValues,NatAssign.values_preserves rowFinish _ i (by simp [rowFinish,NatAssign.Instruction.target];omega),
    ArrayDecodeMachine.output_outside _ i (by simp [ArrayDecodeMachine.ports];omega)]
  rcases hi with hi|hi|hi
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl <;> simp [rowHalved,ArrayDecodeMachine.divModValues,rowPrepared,rowPrepare,
      NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
      NaturalQuotient.workPorts]
  · simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [rowHalved,ArrayDecodeMachine.divModValues,rowPrepared,rowPrepare,
      NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
      NaturalQuotient.workPorts]
  · rw [ite_eq_left hi]
    exact (rowHalved_fields v).2.2.2 i hi

#print axioms rowValues_coordinates
end Maxwell.Continuum.Calibration.SeedRoot
