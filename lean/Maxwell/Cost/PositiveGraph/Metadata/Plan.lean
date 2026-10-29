import Maxwell.Cost.Structured.NatAssign
import Maxwell.Cost.BankArray.Common

namespace Maxwell.Cost.PositiveGraph.Metadata
open Structured
open RationalAccumulator (Word Blank)

def ids : Finset ℕ := {90,116} ∪ Finset.Icc 140 159

def initial (width dimension count i : ℕ) : ℕ :=
  if i=90 then width else if i=116 then count else if i=154 then dimension else 0

/-- A fixed finite list of actual unsigned-arithmetic routines constructs
all graph sizes and nonoverlapping array bases. -/
def statements : List NatAssign.Instruction := [
  .literal 155 3, .copy 90 140, .add 155 140,
  .copy 154 141, .add 154 141, .copy 141 154, .add 116 141,
  .copy 116 142, .add 116 142, .copy 142 153, .add 153 142,
  .copy 142 143, .multiply 140 143,
  .copy 141 156, .add 141 156, .copy 143 144, .add 156 144,
  .copy 142 157, .add 142 157, .copy 144 145, .add 157 145,
  .literal 147 4, .literal 148 8, .literal 149 2, .literal 150 2,
  .literal 155 0, .literal 156 0, .literal 157 0]

def numericCode : Code := NatAssign.code statements
def numericPrice (width dimension count : ℕ) : ℕ :=
  NatAssign.price statements (initial width dimension count)

theorem valid : ∀ a ∈ statements, a.Valid ids := by
  simp [statements,NatAssign.Instruction.Valid,ids]
theorem ids_lower : ∀ i ∈ ids, 4 ≤ i := by
  intro i hi
  simp only [ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
  omega

structure Numeric (width dimension count : ℕ) (s : BitRAMState) : Prop where
  widthWord : Word s 140 (width+3)
  vertices : Word s 141 (2*dimension+count)
  incidences : Word s 142 (4*count)
  counterBase : Word s 143 (4*count*(width+3))
  rankBase : Word s 144 (4*count*(width+3)+2*(2*dimension+count))
  diagonalBase : Word s 145 (4*count*(width+3)+2*(2*dimension+count)+2*(4*count))
  four : Word s 147 4
  clockFour : Word s 148 8
  two : Word s 149 2
  clockTwo : Word s 150 2
  endpointBase : Word s 151 0
  edges : Word s 153 (2*count)
  doubledDimension : Word s 154 (2*dimension)
  temporary : ∀ i, 155 ≤ i → i ≤ 159 → Blank s i

set_option maxRecDepth 16384 in
set_option maxHeartbeats 600000 in
theorem numeric_of_bank (width dimension count : ℕ) (s : BitRAMState)
    (hb : NatAssign.Bank ids (NatAssign.values statements (initial width dimension count)) s) :
    Numeric width dimension count s := by
  have getWord (i : ℕ) (hi : 140 ≤ i) (hj : i ≤ 159) := hb i (by simp [ids]; omega)
  constructor
  · convert getWord 140 (by omega) (by omega) using 1
    all_goals simp [NatAssign.values,statements,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
    all_goals ring
  · convert getWord 141 (by omega) (by omega) using 1
    all_goals simp [NatAssign.values,statements,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
    all_goals ring
  · convert getWord 142 (by omega) (by omega) using 1
    all_goals simp [NatAssign.values,statements,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
    all_goals ring
  · convert getWord 143 (by omega) (by omega) using 1
    all_goals simp [NatAssign.values,statements,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
    all_goals ring
  · convert getWord 144 (by omega) (by omega) using 1
    all_goals simp [NatAssign.values,statements,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
    all_goals ring
  · convert getWord 145 (by omega) (by omega) using 1
    all_goals simp [NatAssign.values,statements,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
    all_goals ring
  · convert getWord 147 (by omega) (by omega) using 1
    all_goals simp [NatAssign.values,statements,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
  · convert getWord 148 (by omega) (by omega) using 1
    all_goals simp [NatAssign.values,statements,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
  · convert getWord 149 (by omega) (by omega) using 1
    all_goals simp [NatAssign.values,statements,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
  · convert getWord 150 (by omega) (by omega) using 1
    all_goals simp [NatAssign.values,statements,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
  · convert getWord 151 (by omega) (by omega) using 1
    all_goals simp [NatAssign.values,statements,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
  · convert getWord 153 (by omega) (by omega) using 1
    all_goals simp [NatAssign.values,statements,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
    all_goals ring
  · convert getWord 154 (by omega) (by omega) using 1
    all_goals simp [NatAssign.values,statements,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial]
    all_goals ring
  · intro i hi hj
    have h := getWord i (by omega) hj
    interval_cases i
    all_goals apply (RationalAccumulator.zero_word_iff_blank s _).mp
    all_goals simpa [NatAssign.values,statements,NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,initial,Function.update_apply] using h

end Maxwell.Cost.PositiveGraph.Metadata
