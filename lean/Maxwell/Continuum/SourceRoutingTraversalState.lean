import Maxwell.Continuum.SourceRoutingTraversalController
import Maxwell.Continuum.SourceRoutingTraversalPrefix

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Traversal
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀i,i=4 ∨ 10 ≤ i→i≠37→i∉Division.work→i∉PrivateNode.banks→i≠831→i≠830→t.tapes i=s.tapes i

theorem Frame.refl (s : BitRAMState) : Frame s s := ⟨rfl,rfl,rfl,fun _ _ _ _ _ _ _ => rfl⟩
theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (j : Frame t u) : Frame s u :=
  ⟨j.inputHead.trans h.inputHead,j.randomCursor.trans h.randomCursor,j.output.trans h.output,
    fun i hi h37 hd hp hc ho => (j.tapes i hi h37 hd hp hc ho).trans (h.tapes i hi h37 hd hp hc ho)⟩
theorem Frame.of_level {s t : BitRAMState} (h : Level.Frame s t) : Frame s t :=
  ⟨h.inputHead,h.randomCursor,h.output,fun i hi h37 hd hp hc _ => h.tapes i hi h37 hd hp hc⟩

def width (heap rows total : ℕ) : ℕ :=
  Level.uniformWidth (ControllerWidth.baseWidth heap (2^(total+rows)) (total+rows+1) total)

structure Setup (v : ℕ→ℕ) (heap rows total : ℕ) : Prop where
  positive : 1 ≤ total
  coordinates : Coordinates.Stored v heap (2^(total+rows)) (total+rows+1) 1
    (2^(total-1+rows)) (total-1+rows+1) 0
  population : v 813=2
  zero : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0
  words : ∀i∈Division.ids,(v i).bits.length ≤ width heap rows total

structure State (v : ℕ→ℕ) (heap rows total : ℕ) (root : Targets.Target rows total)
    (processed : ℕ) (start : BitRAMState) (s : Store) : Prop where
  bank : NatAssign.Bank Division.ids (values v processed) s.val
  clean : PrivateVisit.Clean s
  scratch : Blank s.val 839
  counter : Blank s.val 831
  outputs : Prefix heap rows total root (processed+1) s.val.memory
  frame : Frame start s.val
  memory : Memory.Frame heap ((2^total-1)*stride (2^(total+rows)) (total+rows+1)) start.memory s.val.memory

theorem State.transfer {v : ℕ→ℕ} {heap rows total processed : ℕ} {root : Targets.Target rows total}
    {start : BitRAMState} {s t : Store} (hs : State v heap rows total root processed start s)
    (keep : ∀i,i≠830→t.val.tapes i=s.val.tapes i) (hm : t.val.memory=s.val.memory)
    (hf : Frame s.val t.val) : State v heap rows total root processed start t := by
  refine ⟨?_,?_,RationalAccumulator.blank_of_eq (keep 839 (by decide)) hs.scratch,
    RationalAccumulator.blank_of_eq (keep 831 (by decide)) hs.counter,?_,hs.frame.trans hf,?_⟩
  · intro i hi
    apply RationalAccumulator.word_of_eq (keep i ?_) (hs.bank i hi)
    intro he;subst i;exact (show (830 : ℕ)∉Division.ids by decide) hi
  · apply (Workspace.clean_iff t).mpr
    intro i hi
    apply RationalAccumulator.blank_of_eq (keep i ?_) ((Workspace.clean_iff s).mp hs.clean i hi)
    intro he;subst i;exact (show (830 : ℕ)∉Workspace.ids by decide) hi
  · simpa only [hm] using hs.outputs
  · simpa only [hm] using hs.memory

theorem State.counter_step {v : ℕ→ℕ} {heap rows total processed : ℕ} {root : Targets.Target rows total}
    {start : BitRAMState} {s t : Store} (hs : State v heap rows total root processed start s)
    (hf : CountedShifted.Frame 830 s t) : State v heap rows total root processed start t :=
  hs.transfer hf.2.2.2.2.2.1 hf.2.2.1
    ⟨hf.2.1,hf.2.2.2.1,hf.2.2.2.2.1,fun i _ _ _ _ _ hi => hf.2.2.2.2.2.1 i hi⟩

theorem State.clear {v : ℕ→ℕ} {heap rows total processed : ℕ} {root : Targets.Target rows total}
    {start : BitRAMState} {s t : Store} (hs : State v heap rows total root processed start s)
    (hf : BinaryPrecision.Frame {830} s.val t.val) : State v heap rows total root processed start t :=
  hs.transfer (fun i hi => hf.tapes i (by simpa using hi)) hf.memory
    ⟨hf.inputHead,hf.randomCursor,hf.output,fun i _ _ _ _ _ hi => hf.tapes i (by simpa using hi)⟩

theorem memory_widen (heap rows total d count : ℕ) (hd : d+1 ≤ total) (hc : count ≤ 2^d)
    (before after : ℕ→Bool)
    (hf : Memory.Frame (block heap (2^(total+rows)) (total+rows+1) (2^d-1))
      (count*stride (2^(total+rows)) (total+rows+1)) before after) :
    Memory.Frame heap ((2^total-1)*stride (2^(total+rows)) (total+rows+1)) before after := by
  intro p hp
  apply hf p
  have positive : 0<(2 : ℕ)^d := by positivity
  have powbound : (2 : ℕ)^(d+1) ≤ 2^total := Nat.pow_le_pow_right (by decide) hd
  rw [pow_succ] at powbound
  have mulbound:=Nat.mul_le_mul_right (stride (2^(total+rows)) (total+rows+1))
    (show 2^d-1+count ≤ 2^total-1 by omega)
  dsimp only [block]
  rcases hp with hp|hp
  · left;omega
  · right;nlinarith only [mulbound,hp]

#print axioms State.counter_step
#print axioms memory_widen
end Maxwell.Cost.RoutingPorts.Complete.Tree.Traversal
