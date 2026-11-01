import Maxwell.Cost.Structured.NatAssign
import Maxwell.Cost.Structured.TapeInterval

/-! Arithmetic tape footprints depend on register identifiers, never on
the values or lengths of literal operands. -/
namespace Maxwell.Cost
open Structured
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem BinaryPrecision.writeCode_outside (target lo hi : ℕ) (outside : target<lo ∨hi ≤ target)
    (bits : List Bool) : (writeCode target bits).outsideTapes lo hi=true := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp [writeCode,Code.outsideTapes,PowerOfTwo.appendBit,Code.atom,BitRAM.outsideTapes,
      BitRAMInstruction.outsideTapes,outside,ih]

theorem BinaryPrecision.literalCode_outside (target value lo hi : ℕ)
    (outside : target<lo ∨hi ≤ target) : (literalCode target value).outsideTapes lo hi=true := by
  simp [literalCode,Code.outsideTapes,writeCode_outside target lo hi outside,
    BitRAM.outsideTapes,Rewind.program,BitRAMInstruction.outsideTapes,outside]

namespace Structured.NatAssign

theorem Instruction.outsideTapes (instruction : Instruction) (ids : Finset ℕ) (lo hi : ℕ)
    (valid : instruction.Valid ids) (low : 4 ≤ lo)
    (outside : ∀i∈ids,i<lo ∨hi ≤ i) : instruction.code.outsideTapes lo hi=true := by
  cases instruction with
  | literal target value =>
    have h:=outside target valid
    simp [Instruction.code,Code.outsideTapes,BitRAM.outsideTapes,TapeOps.clear,
      BitRAMInstruction.outsideTapes,BinaryPrecision.literalCode_outside target value lo hi h,h]
  | copy source target =>
    have hs:=outside source valid.1
    have ht:=outside target valid.2.1
    simp [Instruction.code,WordReplace.code,Code.outsideTapes,BitRAM.outsideTapes,
      TapeOps.clear,WordTransfer.clone,Copy.program,Rewind.program,
      BitRAMInstruction.outsideTapes,BitRAMInstruction.relocate,hs,ht]
  | add source target =>
    have hs:=outside source valid.1
    have ht:=outside target valid.2.1
    simp (disch:=omega) [Instruction.code,DecoderConstants.addCode,Code.outsideTapes,
      WordTransfer.clone,Copy.program,PadWord.program,StoredAdd.program,WordTransfer.move,
      TapeOps.copyClear,Rewind.program,RewindOvershoot.program,RewindOvershoot.preamble,
      BitRAM.link,rippleAdder,NormalizeWord.program,ScanForward.program,TapeOps.trim,TapeOps.clear,
      BitRAM.outsideTapes,BitRAMInstruction.outsideTapes,BitRAMInstruction.relocate,hs,ht]
    omega
  | multiply source target =>
    have hs:=outside source valid.1
    have ht:=outside target valid.2.1
    simp (disch:=omega) [Instruction.code,DecoderTerm.multiplyCode,Code.outsideTapes,
      WordTransfer.clone,Copy.program,PadWord.program,StoredProduct.program,TapeOps.copyClear,
      Rewind.program,HornerMultiply.program,rippleAdder,RewindOvershoot.program,
      RewindOvershoot.preamble,BitRAM.link,NormalizeWord.program,ScanForward.program,TapeOps.trim,
      TapeOps.clear,BitRAM.outsideTapes,BitRAMInstruction.outsideTapes,BitRAMInstruction.relocate,hs,ht]
    omega

theorem code_outside (instructions : List Instruction) (ids : Finset ℕ) (lo hi : ℕ)
    (valid : ∀a∈instructions,a.Valid ids) (low : 4 ≤ lo)
    (outside : ∀i∈ids,i<lo ∨hi ≤ i) : (code instructions).outsideTapes lo hi=true := by
  induction instructions with
  | nil => rfl
  | cons a rest ih =>
    simp only [code,Code.outsideTapes,Bool.and_eq_true]
    exact ⟨a.outsideTapes ids lo hi (valid a (by simp)) low outside,
      ih (fun q hq=>valid q (List.mem_cons_of_mem _ hq))⟩

#print axioms code_outside
end Structured.NatAssign
end Maxwell.Cost
