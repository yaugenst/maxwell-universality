import Maxwell.Cost.CalibrationMatrix.GenerationWords
import Maxwell.Cost.CalibrationMatrix.GenerationPrefix
import Maxwell.Cost.CalibrationMatrix.MemoryFrame
import Maxwell.Cost.BankArray.Increment
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.CalibrationMatrix.Generation
open Structured BankArray
open RationalAccumulator (Blank)
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def Data.output {R : ℕ} (d : Data R) : OutputLayout := ⟨d.positiveBase,d.negativeBase⟩

structure LoopFrame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ∉ work → i ≠ 102 → i ≠ 136 → t.tapes i = s.tapes i

theorem LoopFrame.refl (s : BitRAMState) : LoopFrame s s := ⟨rfl,rfl,rfl,fun _ _ _ _ => rfl⟩
theorem LoopFrame.trans {s t u : BitRAMState} (h : LoopFrame s t) (k : LoopFrame t u) : LoopFrame s u :=
  ⟨k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i hi hx hc => (k.tapes i hi hx hc).trans (h.tapes i hi hx hc)⟩

theorem LoopFrame.of_cell {s t : BitRAMState} (h : Frame s t) : LoopFrame s t :=
  ⟨h.inputHead,h.randomCursor,h.output,fun i hi _ _ => h.tapes i hi⟩

theorem LoopFrame.of_counter {s t : Store} (h : CountedShifted.Frame 136 s t) : LoopFrame s.val t.val :=
  ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,fun i _ _ hc => h.2.2.2.2.2.1 i hc⟩

theorem workspace_of_tapes {s t : BitRAMState} (h : Workspace s)
    (keep : ∀ i ∈ work, t.tapes i = s.tapes i) : Workspace t :=
  fun i hi => RationalAccumulator.blank_of_eq (keep i hi) (h i hi)

theorem Workspace.scratch {s : BitRAMState} (h : Workspace s) : Scratch s :=
  ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),
    h 5 (by decide),h 6 (by decide),h 8 (by decide),h 9 (by decide)⟩

theorem Stored.increment {R : ℕ} {d : Data R} {index : List Bool} {s t : BitRAMState}
    (h : Stored d index s) (keep : ∀ i, i ≠ 102 → t.tapes i = s.tapes i)
    (hindex : Word t 102 (Increment.bits index)) : Stored d (Increment.bits index) t :=
  ⟨word_of_eq (keep 100 (by decide)) h.width,word_of_eq (keep 101 (by decide)) h.clock,hindex,
    word_of_eq (keep 110 (by decide)) h.positiveBase,word_of_eq (keep 111 (by decide)) h.negativeBase,
    word_of_eq (keep 121 (by decide)) h.radix,word_of_eq (keep 122 (by decide)) h.dimension,
    word_of_eq (keep 127 (by decide)) h.residue,word_of_eq (keep 129 (by decide)) h.clock2,
    word_of_eq (keep 130 (by decide)) h.clock5,word_of_eq (keep 131 (by decide)) h.twenty⟩

def Invariant {R : ℕ} (d : Data R) (material : Cell20 → ℚ) (z : ℚ) (D : ℕ)
    (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ (3*cubeWidth R^3)^2 ∧ ∃ index : List Bool,
    addressValue index = (3*cubeWidth R^3)^2-remaining ∧ index.length ≤ ((3*cubeWidth R^3)^2).bits.length ∧
    Stored d index s.val ∧ Workspace s.val ∧
    BitArray.Represents s.val.memory (addressValue d.positiveBase) (addressValue d.width)
      (GenerationPrefix.written (BitArray.snapshot initial.memory (addressValue d.positiveBase)
        (addressValue d.width) ((3*cubeWidth R^3)^2))
        (positiveWords R material z D (addressValue d.width)) ((3*cubeWidth R^3)^2-remaining)) ∧
    BitArray.Represents s.val.memory (addressValue d.negativeBase) (addressValue d.width)
      (GenerationPrefix.written (BitArray.snapshot initial.memory (addressValue d.negativeBase)
        (addressValue d.width) ((3*cubeWidth R^3)^2))
        (negativeWords R material z D (addressValue d.width)) ((3*cubeWidth R^3)^2-remaining)) ∧
    LoopFrame initial s.val ∧ OutputOutside d.output ((3*cubeWidth R^3)^2) (addressValue d.width) initial s.val

theorem invariant_stable {R : ℕ} (d : Data R) (material : Cell20 → ℚ) (z : ℚ) (D : ℕ)
    (initial : BitRAMState) (n : ℕ) (s t : Store) (hf : CountedShifted.Frame 136 s t)
    (h : Invariant d material z D initial n s) : Invariant d material z D initial n t := by
  obtain ⟨hn,index,hindex,hlen,hs,hw,hp,hm,hfr,hout⟩ := h
  refine ⟨hn,index,hindex,hlen,hs.of_tapes (fun i hi => hf.2.2.2.2.2.1 i ?_),
    workspace_of_tapes hw (fun i hi => hf.2.2.2.2.2.1 i ?_),?_,?_,
    hfr.trans (LoopFrame.of_counter hf),hout.trans (OutputOutside.of_memory hf.2.2.1)⟩
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro heq; subst i; exact (show 136 ∉ work by decide) hi
  · simpa only [hf.2.2.1] using hp
  · simpa only [hf.2.2.1] using hm

end Maxwell.Cost.CalibrationMatrix.Generation
