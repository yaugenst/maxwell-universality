import Maxwell.Cost.ColorAssemble.Correctness
import Maxwell.Cost.ChildPermutation.LoopSupport

namespace Maxwell.Cost.ColorAssemble
open Structured
open ChildPermutation (Layout Config Workspace LoopFrame Private budget config_update workspace_update)

def LoopInvariant {k : ℕ} (layout : Layout) (d : Data k) (out : Output k)
    (clock childClock : List Bool) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining  ≤  2*(2^k) ∧ ∃ index : List Bool,
    addressValue index=2*(2^k)-remaining ∧ index.length ≤ (2*(2^k)).bits.length ∧
    Config layout index clock childClock s.val ∧ Workspace s.val ∧
    Represents layout s.val.memory d (fillOutput layout d out (2*(2^k)-remaining) (Nat.sub_le _ _)) ∧
    LoopFrame initial s.val ∧ MemoryFrame layout k initial.memory s.val.memory

theorem invariant_stable {k : ℕ} (layout : Layout) (d : Data k) (out : Output k)
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

end Maxwell.Cost.ColorAssemble
