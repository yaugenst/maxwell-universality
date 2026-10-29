import Maxwell.Cost.DoublingPass.Encoding
import Maxwell.Cost.BankArray.ReadBank
import Maxwell.Cost.BankArray.Write
import Maxwell.Cost.BankArray.Minimum
import Maxwell.Cost.IncidencePass.Common

namespace Maxwell.Cost.DoublingPass
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)

structure Config (layout : Layout) (index clock : List Bool) (s : BitRAMState) : Prop where
  width : Word s 80 layout.width.bits
  index : Word s 81 index
  oldJump : Word s 82 layout.oldJump.bits
  clock : Word s 83 clock
  oldMinimum : Word s 84 layout.oldMinimum.bits
  newJump : Word s 85 layout.newJump.bits
  newMinimum : Word s 86 layout.newMinimum.bits

def Private (i : ℕ) : Prop := 88 ≤ i ∧ i ≤ 92

def Frame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i = 4 ∨ 10 ≤ i → ¬Private i → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨hi, hr, ho, ht, hg⟩
  rcases k with ⟨ki, kr, ko, kt, kg⟩
  exact ⟨ki.trans hi, kr.trans hr, ko.trans ho,
    fun i hh hp => (kt i hh hp).trans (ht i hh hp),
    fun i h15 h24 h25 h26 h27 h28 h29 =>
      (kg i h15 h24 h25 h26 h27 h28 h29).trans (hg i h15 h24 h25 h26 h27 h28 h29)⟩

theorem Frame.of_bank {s t : BitRAMState} (h : BankArray.Frame s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi _ => h.2.2.2.1 i hi, h.2.2.2.2⟩

theorem Frame.of_except {bank : ℕ} {s t : BitRAMState}
    (hb : Private bank) (h : BankArray.FrameExcept bank s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1,
    fun i hi hp => h.2.2.2.1 i hi (by intro he; exact hp (he ▸ hb)), h.2.2.2.2⟩

theorem Frame.of_clear {bank : ℕ} {s t : BitRAMState}
    (hb : Private bank) (h : TapeOps.Frame bank bank s t) : Frame s t := by
  have hf := WordTransfer.frame_of_copy h
  exact ⟨hf.2.1, hf.2.2.2.1, hf.2.2.2.2.1,
    fun i _ hp => hf.2.2.2.2.2.1 i (by intro he; exact hp (he ▸ hb))
      (by intro he; exact hp (he ▸ hb)),
    fun i _ h24 h25 h26 h27 _ _ => hf.2.2.2.2.2.2 i h24 h25 h26 h27⟩

theorem Config.of_frame {layout : Layout} {index clock : List Bool}
    {s t : BitRAMState} (h : Frame s t) (c : Config layout index clock s) : Config layout index clock t := by
  constructor
  · exact BankArray.word_of_eq (h.2.2.2.1 80 (by omega) (by simp [Private])) c.width
  · exact BankArray.word_of_eq (h.2.2.2.1 81 (by omega) (by simp [Private])) c.index
  · exact BankArray.word_of_eq (h.2.2.2.1 82 (by omega) (by simp [Private])) c.oldJump
  · exact BankArray.word_of_eq (h.2.2.2.1 83 (by omega) (by simp [Private])) c.clock
  · exact BankArray.word_of_eq (h.2.2.2.1 84 (by omega) (by simp [Private])) c.oldMinimum
  · exact BankArray.word_of_eq (h.2.2.2.1 85 (by omega) (by simp [Private])) c.newJump
  · exact BankArray.word_of_eq (h.2.2.2.1 86 (by omega) (by simp [Private])) c.newMinimum

def Workspace (s : BitRAMState) : Prop :=
  BankArray.Scratch s ∧ Blank s 7 ∧ ∀ i, Private i → Blank s i

def budget (layout : Layout) (index : List Bool) : ℕ :=
  layout.width + layout.width.bits.length + index.length + layout.oldJump.bits.length +
    layout.oldMinimum.bits.length + layout.newJump.bits.length + layout.newMinimum.bits.length + 10

end Maxwell.Cost.DoublingPass
