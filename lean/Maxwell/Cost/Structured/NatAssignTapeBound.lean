import Maxwell.Cost.Structured.NatAssign
import Maxwell.Cost.Structured.TapeBound

/-! Tape bounds for natural arithmetic depend only on the fixed register
identifiers, not on operand values or literal-word lengths. -/
namespace Maxwell.Cost
open Structured
set_option maxHeartbeats 1000000

theorem TapeOps.clear_tapeBound (target : ℕ) : (clear target).tapeBound=target+1 := by
  simp [clear,BitRAM.tapeBound,BitRAMInstruction.tapeBound]

theorem Rewind.tapeBound (target : ℕ) : (program target).tapeBound=target+1 := by
  simp [program,BitRAM.tapeBound,BitRAMInstruction.tapeBound]

theorem WordTransfer.clone_tapeBound (source target : ℕ) :
    (clone source target).tapeBound=max (source+1) (target+1) := by
  simp [clone,Copy.program,Rewind.program,BitRAM.tapeBound,
    BitRAMInstruction.tapeBound,BitRAMInstruction.relocate,max_comm]

theorem BinaryPrecision.writeCode_tapeBound (target : ℕ) (bits : List Bool) :
    (writeCode target bits).tapeBound≤ target+1 := by
  induction bits with
  | nil => simp [writeCode,Code.tapeBound]
  | cons bit bits ih =>
    simpa [writeCode,Code.tapeBound,PowerOfTwo.appendBit,Code.atom,
      BitRAM.tapeBound,BitRAMInstruction.tapeBound] using ih

theorem BinaryPrecision.literalCode_tapeBound (target n : ℕ) :
    (literalCode target n).tapeBound≤ target+1 := by
  simp only [literalCode,Code.tapeBound,max_le_iff,Rewind.tapeBound,le_refl,and_true]
  exact writeCode_tapeBound target n.bits

theorem WordReplace.tapeBound (source target : ℕ) :
    (code source target).tapeBound=max (source+1) (target+1) := by
  simp [code,Code.tapeBound,TapeOps.clear_tapeBound,WordTransfer.clone_tapeBound]

theorem DecoderConstants.addCode_tapeBound (source target N : ℕ)
    (hN : 4≤ N) (hs : source<N) (ht : target<N) : (addCode source target).tapeBound≤ N := by
  simp [addCode,Code.tapeBound,WordTransfer.clone,Copy.program,PadWord.program,
    StoredAdd.program,WordTransfer.move,TapeOps.copyClear,Rewind.program,
    RewindOvershoot.program,RewindOvershoot.preamble,BitRAM.link,rippleAdder,
    NormalizeWord.program,ScanForward.program,TapeOps.trim,
    TapeOps.clear,BitRAM.tapeBound,BitRAMInstruction.tapeBound,BitRAMInstruction.relocate]
  omega

theorem DecoderTerm.multiplyCode_tapeBound (source target N : ℕ)
    (hN : 4≤ N) (hs : source<N) (ht : target<N) : (multiplyCode source target).tapeBound≤ N := by
  simp [multiplyCode,Code.tapeBound,WordTransfer.clone,Copy.program,PadWord.program,
    StoredProduct.program,TapeOps.copyClear,Rewind.program,HornerMultiply.program,rippleAdder,
    RewindOvershoot.program,RewindOvershoot.preamble,BitRAM.link,
    NormalizeWord.program,ScanForward.program,TapeOps.trim,TapeOps.clear,
    BitRAM.tapeBound,BitRAMInstruction.tapeBound,BitRAMInstruction.relocate]
  omega

namespace Structured.NatAssign

theorem Instruction.tapeBound_le (instruction : Instruction) (ids : Finset ℕ) (N : ℕ)
    (valid : instruction.Valid ids) (hN : 4≤ N) (bound : ∀i∈ids,i<N) :
    instruction.code.tapeBound≤ N := by
  cases instruction with
  | literal target value =>
    exact max_le ((TapeOps.clear_tapeBound target).le.trans (by have := bound target valid;omega))
      ((BinaryPrecision.literalCode_tapeBound target value).trans (by have := bound target valid;omega))
  | copy source target =>
    change (WordReplace.code source target).tapeBound≤ N
    rw [WordReplace.tapeBound]
    exact max_le (by have := bound source valid.1;omega) (by have := bound target valid.2.1;omega)
  | add source target =>
    exact DecoderConstants.addCode_tapeBound source target N hN (bound source valid.1) (bound target valid.2.1)
  | multiply source target =>
    exact DecoderTerm.multiplyCode_tapeBound source target N hN (bound source valid.1) (bound target valid.2.1)

theorem code_tapeBound_le (instructions : List Instruction) (ids : Finset ℕ) (N : ℕ)
    (valid : ∀instruction∈instructions,instruction.Valid ids) (hN : 4≤ N)
    (bound : ∀i∈ids,i<N) : (code instructions).tapeBound≤ N := by
  induction instructions with
  | nil => exact Nat.zero_le N
  | cons instruction rest ih =>
    exact max_le (instruction.tapeBound_le ids N (valid instruction (by simp)) hN bound)
      (ih (fun a ha => valid a (List.mem_cons_of_mem _ ha)))

#print axioms code_tapeBound_le
end Structured.NatAssign
end Maxwell.Cost
