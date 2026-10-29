import Maxwell.Cost.ChildPermutation.PrepareClock
import Maxwell.Cost.ChildPermutation.PrepareCount
import Maxwell.Cost.ChildPermutation.PrepareWidth

namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

def MetadataPrivate (i : ℕ) : Prop := i=87 ∨ i=120 ∨ i=121 ∨ i=127 ∨ i=128

def MetadataFrame (s t : BitRAMState) : Prop :=
  t.inputHead=s.inputHead ∧ t.memory=s.memory ∧ t.randomCursor=s.randomCursor ∧ t.output=s.output ∧
  (∀ i, ¬MetadataPrivate i → t.tapes i=s.tapes i) ∧
  (∀ i, 15 ≤ i → i<24 ∨ 31 < i → t.registers i=s.registers i)

theorem MetadataFrame.trans {s t u : BitRAMState} (h : MetadataFrame s t) (j : MetadataFrame t u) : MetadataFrame s u :=
  ⟨j.1.trans h.1,j.2.1.trans h.2.1,j.2.2.1.trans h.2.2.1,j.2.2.2.1.trans h.2.2.2.1,
   fun i hi => (j.2.2.2.2.1 i hi).trans (h.2.2.2.2.1 i hi),
   fun i hi hr => (j.2.2.2.2.2 i hi hr).trans (h.2.2.2.2.2 i hi hr)⟩

theorem MetadataFrame.of_transfer {source target : ℕ} {s t : BitRAMState}
    (keep : ∀ i, ¬MetadataPrivate i → t.tapes i=s.tapes i) (h : WordTransfer.Frame source target s t) : MetadataFrame s t :=
  ⟨h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,keep,
   fun i _ hr => h.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)⟩

theorem MetadataFrame.of_bank {target : ℕ} {s t : BitRAMState}
    (hm : t.memory=s.memory) (keep : ∀ i, ¬MetadataPrivate i → t.tapes i=s.tapes i)
    (h : BankArray.FrameExcept target s t) : MetadataFrame s t :=
  ⟨h.1,hm,h.2.1,h.2.2.1,keep,
   fun i hi hr => h.2.2.2.2 i hi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem MetadataFrame.workspace {s t : BitRAMState} (h : MetadataFrame s t) (w : Workspace s) : Workspace t :=
  DoublingInit.workspace_of_tapes (fun i hi => h.2.2.2.2.1 i (by
    rcases hi with hi | hi
    · dsimp [MetadataPrivate]; omega
    · simp only [DoublingInit.Private,DoublingPass.Private] at hi
      dsimp [MetadataPrivate]; omega)) w

structure Before (layout : Layout) (clock : List Bool) (s : BitRAMState) : Prop where
  width : Word s 80 layout.parentWidth.bits
  index : Word s 81 []
  clock : Word s 83 clock
  colorBase : Word s 85 layout.colors.bits
  one : Word s 86 [true]
  parent : Word s 100 layout.parentForward.bits
  bases : ∀ i : Fin 4, Word s (122+i.val) (layout.outputBase i).bits

theorem Before.of_frame {layout : Layout} {clock : List Bool} {s t : BitRAMState}
    (h : MetadataFrame s t) (c : Before layout clock s) : Before layout clock t := by
  have keep (i : ℕ) (hi : ¬MetadataPrivate i) := h.2.2.2.2.1 i hi
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact BankArray.word_of_eq (keep 80 (by simp [MetadataPrivate])) c.width
  · exact BankArray.word_of_eq (keep 81 (by simp [MetadataPrivate])) c.index
  · exact BankArray.word_of_eq (keep 83 (by simp [MetadataPrivate])) c.clock
  · exact BankArray.word_of_eq (keep 85 (by simp [MetadataPrivate])) c.colorBase
  · exact BankArray.word_of_eq (keep 86 (by simp [MetadataPrivate])) c.one
  · exact BankArray.word_of_eq (keep 100 (by simp [MetadataPrivate])) c.parent
  · intro i
    exact BankArray.word_of_eq (keep (122+i.val) (by dsimp [MetadataPrivate]; omega)) (c.bases i)

end Maxwell.Cost.ChildPermutation
