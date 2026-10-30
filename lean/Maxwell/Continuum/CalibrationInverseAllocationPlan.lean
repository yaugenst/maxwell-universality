import Maxwell.Continuum.CalibrationNeumannCopyTarget
import Maxwell.Continuum.CalibrationWidthClock
import Maxwell.Continuum.WordCleanup

/-! Actual layout arithmetic for a wider shared-denominator output table.
Its initial data are the arbitrary bits already present in memory. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine.Allocation

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def clearHeaders : List ℕ := [210,212,213,214,215]
def headerIds : Finset ℕ := {210,212,213,214}
def inputs : Finset ℕ := Finset.Icc 300 310
def ids : Finset ℕ := inputs ∪ headerIds
def targets : Finset ℕ := {210,212,213,214,303,305,306,307}
def changed : Finset ℕ := {0,1,2,3,210,212,213,214,215,216,303,305,306,307}

def plan : List NatAssign.Instruction :=
  [.copy 300 305,.multiply 300 305,.copy 305 306,.add 300 306,.add 300 306,
   .copy 306 307,.multiply 301 307,.copy 301 210,.copy 302 212,
   .copy 302 213,.add 307 213,.copy 213 214,.add 307 214,.literal 303 0]
def clearedValues (v : ℕ → ℕ) (i : ℕ) : ℕ := if i ∈ headerIds then 0 else v i
def outputValues (v : ℕ → ℕ) : ℕ → ℕ := NatAssign.values plan (clearedValues v)

theorem valid : ∀ a ∈ plan, a.Valid ids := by simp [plan,NatAssign.Instruction.Valid,ids,inputs,headerIds]
theorem target_mem : ∀ a ∈ plan, a.target ∈ targets := by simp [plan,NatAssign.Instruction.target,targets]
theorem inputs_ge (i : ℕ) (hi : i ∈ ids) : 4 ≤ i := by
  simp only [ids,inputs,headerIds,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem outputs (v : ℕ → ℕ) :
    outputValues v 210=v 301 ∧ outputValues v 212=v 302 ∧
      outputValues v 213=v 302+tableSize (v 300)*v 301 ∧
      outputValues v 214=v 302+2*tableSize (v 300)*v 301 ∧
      outputValues v 303=0 ∧ outputValues v 300=v 300 ∧
      outputValues v 301=v 301 ∧ outputValues v 302=v 302 ∧ outputValues v 304=v 304 := by
  simp [outputValues,plan,clearedValues,headerIds,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,tableSize]
  constructor <;> ring

def table (n width heap : ℕ) (hw : 0 < width) (memory : ℕ → Bool) : PartArray.Table (tableSize n) where
  width := width.bits
  basePositive := heap.bits
  baseNegative := (heap+tableSize n*width).bits
  baseDenominator := (heap+2*tableSize n*width).bits
  clock := List.replicate width false
  positive := memoryWords memory heap width (tableSize n)
  negative := memoryWords memory (heap+tableSize n*width) width (tableSize n)
  denominator := memoryWords memory (heap+2*tableSize n*width) width (tableSize n)
  width_pos := by rw [Nat.size_eq_bits_len]; exact Nat.size_pos.mpr hw
  clock_length := by simp only [List.length_replicate,addressValue_bits]

theorem table_layout (n width heap : ℕ) (hw : 0 < width) (memory : ℕ → Bool) :
    SourceLayout (table n width heap hw memory) heap := by
  constructor <;> simp only [table,addressValue_bits]

theorem output_values_input (v : ℕ → ℕ) :
    Descriptors.Inputs (outputValues v) (v 300) (v 301) (v 302) 0 (v 304) := by
  obtain ⟨_,_,_,_,hd,hn,hw,hh,hN⟩ := outputs v
  exact ⟨hn,hw,hh,hd,hN⟩

#print axioms outputs
#print axioms table_layout

end Maxwell.Continuum.Calibration.NeumannMachine.Allocation
