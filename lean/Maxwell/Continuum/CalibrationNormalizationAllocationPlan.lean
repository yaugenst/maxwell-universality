import Maxwell.Continuum.ProfileBufferLayout
import Maxwell.Continuum.CalibrationWidthClock
import Maxwell.Continuum.WordCleanup
import Maxwell.Continuum.NatAssignOutputWidth

/-! Fixed metadata arithmetic for the normalized rational coordinate table.
The table starts in arbitrary memory; no zeroed output buffer is required. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def clearHeaders : List ℕ := [210,212,213,214,215]
def headerIds : Finset ℕ := {210,212,213,214}
def inputs : Finset ℕ := {570,571,572,573}
def ids : Finset ℕ := inputs ∪ headerIds
def changed : Finset ℕ := {0,1,2,3,210,212,213,214,215,216,573}
def plan : List NatAssign.Instruction :=
  [.copy 570 573,.multiply 571 573,.copy 571 210,.copy 572 212,
   .copy 572 213,.add 573 213,.copy 213 214,.add 573 214]
def clearedValues (v : ℕ → ℕ) (i : ℕ) : ℕ := if i∈headerIds then 0 else v i
def outputValues (v : ℕ → ℕ) : ℕ → ℕ := NatAssign.values plan (clearedValues v)

theorem valid : ∀ a∈plan, a.Valid ids := by
  simp [plan,NatAssign.Instruction.Valid,ids,inputs,headerIds]

theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i := by
  simp only [ids,inputs,headerIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem outputs (v : ℕ → ℕ) :
    outputValues v 210=v 571 ∧ outputValues v 212=v 572 ∧
    outputValues v 213=v 572+v 570*v 571 ∧
    outputValues v 214=v 572+2*v 570*v 571 ∧
    outputValues v 570=v 570 ∧ outputValues v 571=v 571 ∧ outputValues v 572=v 572 := by
  simp [outputValues,plan,clearedValues,headerIds,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]
  constructor <;> ring

theorem cleared_width (v : ℕ → ℕ) (B : ℕ)
    (hv : ∀ i∈inputs, (v i).bits.length≤B) :
    ∀ i∈ids, (clearedValues v i).bits.length≤B := by
  intro i hi
  by_cases hh : i∈headerIds
  · simp [clearedValues,hh]
  · rw [clearedValues,ite_eq_right hh]
    exact hv i ((Finset.mem_union.mp hi).resolve_right hh)

#print axioms outputs

end Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation
