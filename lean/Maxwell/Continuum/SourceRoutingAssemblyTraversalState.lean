import Maxwell.Continuum.SourceRoutingAssemblyTraversalController
import Maxwell.Continuum.SourceRoutingTraversalState

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyTraversal
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def Frontier (heap rows total : ℕ) (root : Targets.Target rows total) (columns : ℕ)
    (memory : ℕ→Bool) : Prop :=
  ∀d (hd : d+columns=total),∀i : Fin (2^d),
    LabelsAt heap (2^(total+rows)) (total+rows+1) (levelNode d i) rows columns
      (Targets.level rows total d columns root (by omega) i) memory

structure Setup (v : ℕ→ℕ) (heap rows total : ℕ) : Prop where
  positive : 1 ≤ total
  coordinates : AssemblyCoordinates.Stored v heap (2^(total+rows)) (total+rows+1) (total-1) rows 0
  population : v 813=2^(total-1)
  zero : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0
  words : ∀i∈Division.ids,(v i).bits.length ≤ width heap rows total

structure State (v : ℕ→ℕ) (heap rows total : ℕ) (root : Targets.Target rows total)
    (processed : ℕ) (start : BitRAMState) (s : Store) : Prop where
  bank : NatAssign.Bank Division.ids (values v total processed) s.val
  clean : PrivateVisit.Clean s
  scratch : Blank s.val 839
  counter : Blank s.val 831
  outputs : Traversal.Prefix heap rows total root (total-processed) s.val.memory
  labels : Frontier heap rows total root processed s.val.memory
  frame : Traversal.Frame start s.val
  memory : Memory.Frame heap ((2^total-1)*stride (2^(total+rows)) (total+rows+1)) start.memory s.val.memory

theorem State.transfer {v : ℕ→ℕ} {heap rows total processed : ℕ} {root : Targets.Target rows total}
    {start : BitRAMState} {s t : Store} (hs : State v heap rows total root processed start s)
    (keep : ∀i,i≠830→t.val.tapes i=s.val.tapes i) (hm : t.val.memory=s.val.memory)
    (hf : Traversal.Frame s.val t.val) : State v heap rows total root processed start t := by
  refine ⟨?_,?_,RationalAccumulator.blank_of_eq (keep 839 (by decide)) hs.scratch,
    RationalAccumulator.blank_of_eq (keep 831 (by decide)) hs.counter,?_,?_,hs.frame.trans hf,?_⟩
  · intro i hi
    apply RationalAccumulator.word_of_eq (keep i ?_) (hs.bank i hi)
    intro he;subst i;exact (show (830 : ℕ)∉Division.ids by decide) hi
  · apply (Workspace.clean_iff t).mpr
    intro i hi
    apply RationalAccumulator.blank_of_eq (keep i ?_) ((Workspace.clean_iff s).mp hs.clean i hi)
    intro he;subst i;exact (show (830 : ℕ)∉Workspace.ids by decide) hi
  · simpa only [hm] using hs.outputs
  · simpa only [hm] using hs.labels
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

theorem State.root_labels {v : ℕ→ℕ} {heap rows total : ℕ} {root : Targets.Target rows total}
    {start : BitRAMState} {s : Store} (hs : State v heap rows total root total start s) :
    LabelsAt heap (2^(total+rows)) (total+rows+1) 0 rows total root s.val.memory := by
  have hh:=hs.labels 0 (by omega) (⟨0,by simp⟩ : Fin (2^0))
  simpa only [levelNode,pow_zero,Nat.sub_self,Nat.add_zero,Targets.level,
    Targets.family,Targets.castTarget] using hh

#print axioms State.counter_step
#print axioms State.root_labels
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyTraversal
