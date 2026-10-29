import Maxwell.Cost.ChildPermutation.Common
import Maxwell.Cost.ChildPermutation.Correctness
import Maxwell.Cost.BankArray.Increment
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

/-- Traversal may update its running index and countdown in addition to the
already private step scratch; all other persistent banks remain unchanged. -/
def LoopFrame (s t : BitRAMState) : Prop :=
  t.inputHead=s.inputHead ∧ t.randomCursor=s.randomCursor ∧ t.output=s.output ∧
  (∀ i, i=4 ∨ 10 ≤ i → i ≠ 81 → i ≠ 126 → ¬ Private i → t.tapes i=s.tapes i) ∧
  (∀ i, 15 ≤ i → i < 24 ∨ 31 < i → t.registers i=s.registers i)

theorem LoopFrame.refl (s : BitRAMState) : LoopFrame s s := by simp [LoopFrame]

theorem LoopFrame.trans {s t u : BitRAMState} (h : LoopFrame s t) (j : LoopFrame t u) : LoopFrame s u :=
  ⟨j.1.trans h.1,j.2.1.trans h.2.1,j.2.2.1.trans h.2.2.1,
    fun i hi h81 h126 hp => (j.2.2.2.1 i hi h81 h126 hp).trans (h.2.2.2.1 i hi h81 h126 hp),
    fun i hi hr => (j.2.2.2.2 i hi hr).trans (h.2.2.2.2 i hi hr)⟩

theorem LoopFrame.of_step {s t : BitRAMState} (h : Frame s t) : LoopFrame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi _ _ hp => h.2.2.2.1 i hi hp,h.2.2.2.2⟩

theorem LoopFrame.of_increment {s t : BitRAMState} (h : BankArray.FrameExcept 81 s t) : LoopFrame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi h81 _ _ => h.2.2.2.1 i hi h81,
    fun i hi hr => h.2.2.2.2 i hi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem LoopFrame.of_counter {s t : Store} (h : CountedShifted.Frame 126 s t) : LoopFrame s.val t.val :=
  ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,fun i _ _ h126 _ => h.2.2.2.2.2.1 i h126,
    fun i hi hr => h.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)⟩

theorem config_update {layout : Layout} {index index' clock childClock : List Bool}
    {s t : BitRAMState} (h : ∀ i, i ≠ 81 → i ≠ 126 → t.tapes i=s.tapes i)
    (c : Config layout index clock childClock s) (hi : Word t 81 index') :
    Config layout index' clock childClock t := by
  refine ⟨?_,hi,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact BankArray.word_of_eq (h 80 (by omega) (by omega)) c.parentWidth
  · exact BankArray.word_of_eq (h 83 (by omega) (by omega)) c.clock
  · exact BankArray.word_of_eq (h 86 (by omega) (by omega)) c.one
  · exact BankArray.word_of_eq (h 87 (by omega) (by omega)) c.bitClock
  · exact BankArray.word_of_eq (h 100 (by omega) (by omega)) c.parent
  · exact BankArray.word_of_eq (h 120 (by omega) (by omega)) c.childWidth
  · exact BankArray.word_of_eq (h 121 (by omega) (by omega)) c.childClock
  · intro j
    exact BankArray.word_of_eq (h (122+j.val) (by omega) (by omega)) (c.bases j)
  · exact BankArray.word_of_eq (h 128 (by omega) (by omega)) c.colors

theorem workspace_update {s t : BitRAMState}
    (h : ∀ i, i ≠ 81 → i ≠ 126 → t.tapes i=s.tapes i) (w : Workspace s) : Workspace t := by
  refine ⟨⟨scratch_of_tapes (fun i hi => h i (by omega) (by omega)) w.1.1,
    RationalAccumulator.blank_of_eq (h 7 (by omega) (by omega)) w.1.2.1,?_⟩,
    RationalAccumulator.blank_of_eq (h 37 (by omega) (by omega)) w.2⟩
  intro i hi
  exact RationalAccumulator.blank_of_eq (h i (by dsimp [DoublingPass.Private] at hi; omega)
    (by dsimp [DoublingPass.Private] at hi; omega)) (w.1.2.2 i hi)

theorem MemoryFrame.refl (l : Layout) (k : ℕ) (memory : ℕ → Bool) :
    MemoryFrame l k memory memory := fun _ _ => rfl

def LoopInvariant {k : ℕ} (layout : Layout) (d : Data k) (out : Outputs k)
    (clock childClock : List Bool) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining  ≤  2^k ∧ ∃ index : List Bool,
    addressValue index=2^k-remaining ∧ index.length ≤ (2^k).bits.length ∧
    Config layout index clock childClock s.val ∧ Workspace s.val ∧
    Represents layout s.val.memory d (fillOutputs layout.childWidth d out (2^k-remaining) (Nat.sub_le _ _)) ∧
    LoopFrame initial s.val ∧ MemoryFrame layout k initial.memory s.val.memory

theorem invariant_stable {k : ℕ} (layout : Layout) (d : Data k) (out : Outputs k)
    (clock childClock : List Bool) (initial : BitRAMState) (r : ℕ) (s t : Store)
    (hf : CountedShifted.Frame 126 s t) (h : LoopInvariant layout d out clock childClock initial r s) :
    LoopInvariant layout d out clock childClock initial r t := by
  obtain ⟨hr,index,hi,hl,hc,hw,hrep,hfr,hm⟩ := h
  have keep (i : ℕ) (hi : i ≠ 126) := hf.2.2.2.2.2.1 i hi
  refine ⟨hr,index,hi,hl,config_update (fun i _ hi => keep i hi) hc
    (BankArray.word_of_eq (keep 81 (by omega)) hc.index),
    workspace_update (fun i _ hi => keep i hi) hw,?_,hfr.trans (LoopFrame.of_counter hf),?_⟩
  · simpa only [hf.2.2.1] using hrep
  · simpa only [hf.2.2.1] using hm

end Maxwell.Cost.ChildPermutation
