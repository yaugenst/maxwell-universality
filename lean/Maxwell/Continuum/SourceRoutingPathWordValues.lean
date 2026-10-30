import Maxwell.Continuum.SourceRoutingGeometryAccess
import Maxwell.Continuum.NatAssignOutputWidth

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic
open RationalAccumulator (Word)
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

def axisBank (axis : Fin 3) : ℕ := 1226+axis.val
def wordPrepare (axis : Fin 3) (offset : ℕ) : List NatAssign.Instruction :=
  [.literal 1235 offset,.add (axisBank axis) 1235]
def wordCleanup : List NatAssign.Instruction := [.add 1219 1234,.literal 1235 0]
def wordCode (axis : Fin 3) (offset : ℕ) : Code := .seq (NatAssign.code (wordPrepare axis offset))
  (.seq (BankArray.writeCanonicalCode 1250 1234 1252 1251 1235) (NatAssign.code wordCleanup))
def wordWork : Finset ℕ := {37}∪GeometryArithmetic.work

structure OutputMetadata (width base : ℕ) (clock : List Bool) (s : BitRAMState) : Prop where
  wordWidth : Word s 1250 width
  baseWord : Word s 1252 base
  clockWord : BankArray.Word s 1251 clock

theorem OutputMetadata.frame {width base : ℕ} {clock : List Bool} {s t : BitRAMState}
    (metadata : OutputMetadata width base clock s) (frame : ArchiveFrame wordWork s t) :
    OutputMetadata width base clock t :=
  ⟨RationalAccumulator.word_of_eq (frame.tapes 1250 (by decide) (by decide)) metadata.wordWidth,
    RationalAccumulator.word_of_eq (frame.tapes 1252 (by decide) (by decide)) metadata.baseWord,
    BankArray.word_of_eq (frame.tapes 1251 (by decide) (by decide)) metadata.clockWord⟩

theorem wordPrepare_valid (axis : Fin 3) (offset : ℕ) : ∀a∈wordPrepare axis offset,a.Valid ids := by
  have bound:=axis.isLt
  simp [wordPrepare,NatAssign.Instruction.Valid,ids,controls,axisBank]
  omega

theorem wordCleanup_valid : ∀a∈wordCleanup,a.Valid ids := by
  simp [wordCleanup,NatAssign.Instruction.Valid,ids,controls]

theorem wordPrepare_values (axis : Fin 3) (offset : ℕ) (v : ℕ→ℕ) :
    NatAssign.values (wordPrepare axis offset) v=Function.update v 1235 (v (axisBank axis)+offset) := by
  have different : axisBank axis≠1235 := by dsimp only [axisBank];have := axis.isLt;omega
  simp [wordPrepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,different]

theorem wordCleanup_values (axis : Fin 3) (offset : ℕ) (v : ℕ→ℕ) (one : v 1219=1) (zero : v 1235=0) :
    NatAssign.values wordCleanup (NatAssign.values (wordPrepare axis offset) v)=
      Function.update v 1234 (v 1234+1) := by
  rw [wordPrepare_values]
  funext j
  by_cases h35 : j=1235
  · subst j;simp [wordCleanup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,zero]
  by_cases h34 : j=1234
  · subst j;simp [wordCleanup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,one,Nat.add_comm]
  simp [wordCleanup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,h34,h35]

theorem wordPrepare_width (axis : Fin 3) (offset : ℕ) (v : ℕ→ℕ) (B : ℕ)
    (width : ∀j∈ids,(v j).bits.length ≤ B) (literal : offset.bits.length ≤ B) :
    ∀j∈ids,(NatAssign.values (wordPrepare axis offset) v j).bits.length ≤ 4*(B+1) := by
  have h:=NatAssign.values_width_bound ids (wordPrepare axis offset) (wordPrepare_valid axis offset) v B width
    (by simp [wordPrepare,NatAssign.Instruction.literalWidth,literal])
  intro j hj
  exact (Nat.le_add_right _ _).trans (h j hj)

#print axioms wordCleanup_values
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
