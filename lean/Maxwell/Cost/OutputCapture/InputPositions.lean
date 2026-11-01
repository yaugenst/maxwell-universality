import Maxwell.Cost.OutputCapture.Retained
import Maxwell.Cost.Structured.InputPositions

/-! Capturing a program's emitted stream preserves its proof that input and
random-seed positions are unchanged. The proof follows the compiler and does
not expand a large compiled instruction list. -/
namespace Maxwell.Cost
open Structured

theorem BitRAMInstruction.positions_relocate (base exitPC : ℕ) (i : BitRAMInstruction) :
    (i.relocate base exitPC).protectsInputPositions=i.protectsInputPositions := by
  cases i <;> rfl

theorem Structured.Code.compileAt_positions (body : Code) (base exitPC : ℕ) :
    (body.compileAt base exitPC).all BitRAMInstruction.protectsInputPositions=body.protectsInputPositions := by
  induction body generalizing base exitPC with
  | skip => rfl
  | call machine =>
    simp [Code.compileAt,Code.protectsInputPositions,BitRAM.protectsInputPositions,
      List.all_map,Function.comp_def,BitRAMInstruction.positions_relocate]
  | seq a b ha hb => simp [Code.compileAt,Code.protectsInputPositions,ha,hb]
  | branch r a b ha hb =>
    simp [Code.compileAt,Code.protectsInputPositions,BitRAMInstruction.protectsInputPositions,ha,hb]
  | loop r a ha =>
    simp [Code.compileAt,Code.protectsInputPositions,BitRAMInstruction.protectsInputPositions,ha]

theorem Structured.Code.compile_positions (body : Code) :
    body.compile.protectsInputPositions=body.protectsInputPositions := by
  simp [Code.compile,BitRAM.protectsInputPositions,Code.compileAt_positions,
    BitRAMInstruction.protectsInputPositions]

namespace OutputCapture

theorem program_positions (archive : ℕ) (body : BitRAM)
    (hp : body.protectsInputPositions=true) :
    (program archive body).protectsInputPositions=true := by
  apply List.all_eq_true.mpr
  intro instruction hi
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hi
  have original:=List.all_eq_true.mp hp (body.code[i.val/2]) (List.getElem_mem _)
  dsimp only
  split <;> cases h : body.code[i.val/2] <;>
    simp_all [first,second,BitRAMInstruction.protectsInputPositions]

theorem code_positions (archive : ℕ) (body : Code)
    (hp : body.protectsInputPositions=true) :
    (code archive body).protectsInputPositions=true := by
  change (program archive body.compile).protectsInputPositions &&
    (Rewind.program archive).protectsInputPositions=true
  rw [Bool.and_eq_true]
  refine ⟨program_positions archive body.compile (by rw [Code.compile_positions];exact hp),?_⟩
  rfl

#print axioms code_positions
end OutputCapture
end Maxwell.Cost
