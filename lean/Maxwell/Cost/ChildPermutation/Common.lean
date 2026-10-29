import Maxwell.Cost.ChildPermutation.Encoding
import Maxwell.Cost.ChildPermutation.Select
import Maxwell.Cost.BankArray.ReadBank
import Maxwell.Cost.BankArray.Write
import Maxwell.Cost.BankArray.WriteCanonical
import Maxwell.Cost.Structured.Primitive

namespace Maxwell.Cost.ChildPermutation
open BankArray (Word)
open RationalAccumulator (Blank)

structure Config (layout : Layout) (index clock childClock : List Bool) (s : BitRAMState) : Prop where
  parentWidth : Word s 80 layout.parentWidth.bits
  index : Word s 81 index
  clock : Word s 83 clock
  one : Word s 86 [true]
  bitClock : Word s 87 [false]
  parent : Word s 100 layout.parentForward.bits
  childWidth : Word s 120 layout.childWidth.bits
  childClock : Word s 121 childClock
  bases : ∀ i : Fin 4, Word s (122+i.val) (layout.outputBase i).bits
  colors : Word s 128 layout.colors.bits

abbrev Private := DoublingInit.Private
abbrev Workspace := DoublingInit.Workspace

def Frame (s t : BitRAMState) : Prop :=
  t.inputHead=s.inputHead ∧ t.randomCursor=s.randomCursor ∧ t.output=s.output ∧
  (∀ i, i=4 ∨ 10 ≤ i → ¬Private i → t.tapes i=s.tapes i) ∧
  (∀ i, 15 ≤ i → i<24 ∨ 31 < i → t.registers i=s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (j : Frame t u) : Frame s u :=
  ⟨j.1.trans h.1,j.2.1.trans h.2.1,j.2.2.1.trans h.2.2.1,
   fun i hi hp => (j.2.2.2.1 i hi hp).trans (h.2.2.2.1 i hi hp),
   fun i hi hr => (j.2.2.2.2 i hi hr).trans (h.2.2.2.2 i hi hr)⟩

theorem Frame.of_bank {s t : BitRAMState} (h : BankArray.Frame s t) : Frame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi _ => h.2.2.2.1 i hi,
   fun i hi hr => h.2.2.2.2 i hi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem Frame.of_except {bank : ℕ} {s t : BitRAMState} (hb : Private bank) (h : BankArray.FrameExcept bank s t) : Frame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi hp => h.2.2.2.1 i hi (by intro he; exact hp (he ▸ hb)),
   fun i hi hr => h.2.2.2.2 i hi (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem Frame.of_transfer {source target : ℕ} {s t : BitRAMState}
    (hs : Private source) (ht : Private target) (h : WordTransfer.Frame source target s t) : Frame s t :=
  ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,
   fun i _ hp => h.2.2.2.2.2.1 i (by intro he; exact hp (he ▸ hs)) (by intro he; exact hp (he ▸ ht)),
   fun i _ hr => h.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)⟩

theorem Frame.of_select {s t : BitRAMState} (h : SelectFrame s t) : Frame s t :=
  ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,
   fun i _ hp => h.2.2.2.2.2.1 i
     (by intro he; exact hp (he ▸ (by simp [Private,DoublingInit.Private,DoublingPass.Private])))
     (by intro he; exact hp (he ▸ (by simp [Private,DoublingInit.Private,DoublingPass.Private])))
     (by intro he; exact hp (he ▸ (by simp [Private,DoublingInit.Private,DoublingPass.Private]))),
   fun i _ hr => h.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)⟩

theorem Config.of_frame {layout : Layout} {index clock childClock : List Bool} {s t : BitRAMState}
    (h : Frame s t) (c : Config layout index clock childClock s) : Config layout index clock childClock t := by
  have keep (i : ℕ) (hi : 80 ≤ i) (hp : ¬Private i) := h.2.2.2.1 i (by omega) hp
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact BankArray.word_of_eq (keep 80 (by omega) (by simp [Private,DoublingInit.Private,DoublingPass.Private])) c.parentWidth
  · exact BankArray.word_of_eq (keep 81 (by omega) (by simp [Private,DoublingInit.Private,DoublingPass.Private])) c.index
  · exact BankArray.word_of_eq (keep 83 (by omega) (by simp [Private,DoublingInit.Private,DoublingPass.Private])) c.clock
  · exact BankArray.word_of_eq (keep 86 (by omega) (by simp [Private,DoublingInit.Private,DoublingPass.Private])) c.one
  · exact BankArray.word_of_eq (keep 87 (by omega) (by simp [Private,DoublingInit.Private,DoublingPass.Private])) c.bitClock
  · exact BankArray.word_of_eq (keep 100 (by omega) (by simp [Private,DoublingInit.Private,DoublingPass.Private])) c.parent
  · exact BankArray.word_of_eq (keep 120 (by omega) (by simp [Private,DoublingInit.Private,DoublingPass.Private])) c.childWidth
  · exact BankArray.word_of_eq (keep 121 (by omega) (by simp [Private,DoublingInit.Private,DoublingPass.Private])) c.childClock
  · intro i
    exact BankArray.word_of_eq (keep (122+i.val) (by omega)
      (by simp only [Private,DoublingInit.Private,DoublingPass.Private]; omega)) (c.bases i)
  · exact BankArray.word_of_eq (keep 128 (by omega) (by simp [Private,DoublingInit.Private,DoublingPass.Private])) c.colors

theorem scratch_of_tapes {s t : BitRAMState} (h : ∀ i, i<10 → t.tapes i=s.tapes i)
    (ss : BankArray.Scratch s) : BankArray.Scratch t := by
  rcases ss with ⟨s0,s1,s2,s3,s5,s6,s8,s9⟩
  exact ⟨RationalAccumulator.blank_of_eq (h 0 (by omega)) s0,
    RationalAccumulator.blank_of_eq (h 1 (by omega)) s1,
    RationalAccumulator.blank_of_eq (h 2 (by omega)) s2,
    RationalAccumulator.blank_of_eq (h 3 (by omega)) s3,
    RationalAccumulator.blank_of_eq (h 5 (by omega)) s5,
    RationalAccumulator.blank_of_eq (h 6 (by omega)) s6,
    RationalAccumulator.blank_of_eq (h 8 (by omega)) s8,
    RationalAccumulator.blank_of_eq (h 9 (by omega)) s9⟩

def budget (layout : Layout) (index : List Bool) : ℕ :=
  layout.parentWidth+layout.childWidth+layout.parentWidth.bits.length+layout.childWidth.bits.length+
    index.length+layout.parentForward.bits.length+layout.colors.bits.length+
    layout.leftForward.bits.length+layout.leftBackward.bits.length+
    layout.rightForward.bits.length+layout.rightBackward.bits.length+20

end Maxwell.Cost.ChildPermutation
