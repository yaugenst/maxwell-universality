import Maxwell.Continuum.SourceRoutingLevelMemory
import Maxwell.Cost.Structured.CountedShifted

/-! The routing level invariant contains actual controller words and
actual memory arrays. It survives counter tests and one proved node body. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Level
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀i,i=4 ∨ 10 ≤ i → i≠37 → i∉Division.work → i∉PrivateNode.banks → i≠831 → t.tapes i=s.tapes i

theorem Frame.refl (s : BitRAMState) : Frame s s := ⟨rfl,rfl,rfl,fun _ _ _ _ _ _ => rfl⟩
theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (j : Frame t u) : Frame s u :=
  ⟨j.inputHead.trans h.inputHead,j.randomCursor.trans h.randomCursor,j.output.trans h.output,
    fun i hi h37 hd hp hc => (j.tapes i hi h37 hd hp hc).trans (h.tapes i hi h37 hd hp hc)⟩

theorem Frame.of_step {s t : BitRAMState} (h : Step.Frame s t) : Frame s t :=
  ⟨h.inputHead,h.randomCursor,h.output,fun i hi h37 hd hp _ => h.tapes i hi h37 hd hp⟩
theorem Frame.of_counter {s t : Store} (h : CountedShifted.Frame 831 s t) : Frame s.val t.val :=
  ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,fun i _ _ _ _ hi => h.2.2.2.2.2.1 i hi⟩

structure State {k : ℕ} (p : Plan k) (processed : ℕ) (start : BitRAMState) (s : Store) : Prop where
  bank : NatAssign.Bank Division.ids (values p.initial processed) s.val
  clean : PrivateVisit.Clean s
  scratch : Blank s.val 839
  inputs : p.Inputs s.val.memory
  done : p.Done processed s.val.memory
  frame : Frame start s.val
  memory : Memory.Frame (block p.heap p.rootCount p.rootWidth p.first)
    (processed*stride p.rootCount p.rootWidth) start.memory s.val.memory

theorem State.transfer {k : ℕ} {p : Plan k} {processed : ℕ} {start : BitRAMState} {s t : Store}
    (hs : State p processed start s) (keep : ∀i,i≠831→t.val.tapes i=s.val.tapes i)
    (hm : t.val.memory=s.val.memory) (hf : Frame s.val t.val) : State p processed start t := by
  refine ⟨?_,?_,RationalAccumulator.blank_of_eq (keep 839 (by decide)) hs.scratch,?_,?_,
    hs.frame.trans hf,by simpa only [hm] using hs.memory⟩
  · intro i hi
    apply RationalAccumulator.word_of_eq (keep i ?_) (hs.bank i hi)
    intro he; subst i
    exact (show (831 : ℕ)∉Division.ids by decide) hi
  · apply (Workspace.clean_iff t).mpr
    intro i hi
    apply RationalAccumulator.blank_of_eq (keep i ?_) ((Workspace.clean_iff s).mp hs.clean i hi)
    intro he; subst i
    exact (show (831 : ℕ)∉Workspace.ids by decide) hi
  · simpa only [hm] using hs.inputs
  · simpa only [hm] using hs.done

theorem State.counter {k : ℕ} {p : Plan k} {processed : ℕ} {start : BitRAMState} {s t : Store}
    (hs : State p processed start s) (hf : CountedShifted.Frame 831 s t) : State p processed start t :=
  hs.transfer hf.2.2.2.2.2.1 hf.2.2.1 (Frame.of_counter hf)

theorem State.clear {k : ℕ} {p : Plan k} {processed : ℕ} {start : BitRAMState} {s t : Store}
    (hs : State p processed start s) (hf : BinaryPrecision.Frame {831} s.val t.val) : State p processed start t :=
  hs.transfer (fun i hi => hf.tapes i (by simpa using hi)) hf.memory
    ⟨hf.inputHead,hf.randomCursor,hf.output,fun i _ _ _ _ hi => hf.tapes i (by simpa using hi)⟩

theorem State.step {k : ℕ} (p : Plan k) (processed : ℕ) (hi : processed<p.nodes)
    (input : List Bool) (tape : ℕ→Bool) (start : BitRAMState) (s : Store) (hs : State p processed start s) :
    ∃steps t, Executes input tape Step.code steps s t ∧
      steps ≤ 2^300*(2*2^k+1)*(p.B+2)^3 ∧ State p (processed+1) start t ∧
      t.val.tapes 831=s.val.tapes 831 := by
  let i : Fin p.nodes:=⟨processed,hi⟩
  have forward : Descriptor.output (values p.initial processed) 803+(2*2^k)*(k+2) ≤
      Descriptor.output (values p.initial processed) 800 := by
    rw [p.address processed hi]
    exact (p.forward_before processed hi).trans (p.block_mono processed)
  have backward : Descriptor.output (values p.initial processed) 804+(2*2^k)*(k+2) ≤
      Descriptor.output (values p.initial processed) 800 := by
    rw [p.address processed hi]
    exact (p.backward_before processed hi).trans (p.block_mono processed)
  obtain ⟨steps,t,he,hcost,bt,zt,t839,rep,ft,mt⟩ := Step.executes (values p.initial processed) k p.B p.B_lower
    (p.two processed hi) (p.count processed hi) (p.width processed hi) (p.zero processed hi)
    (p.words processed hi) (p.data i) (p.colors i) (p.separated processed hi) forward backward
    input tape s hs.bank hs.clean hs.scratch (hs.inputs i).1 (hs.inputs i).2
  have mf : Memory.Frame (block p.heap p.rootCount p.rootWidth (p.first+processed))
      (stride p.rootCount p.rootWidth) s.val.memory t.val.memory := by
    change SplitNode.MemoryFrame (p.layout i) k s.val.memory t.val.memory at mt
    rw [p.layout_eq i] at mt
    exact Memory.split_frame p.heap p.rootCount p.rootWidth (p.first+processed) k p.count_fits p.width_fits _ _ _ _ mt
  have newOutput : Outputs.Stored (p.layout i) k (p.data i) t.val.memory := by
    apply Outputs.of_represents
    have hw : ((p.layout i).child (2*2^k)).childWidth=k+1 := by
      rw [p.layout_eq]
      change k+2-1=k+1
      omega
    change ChildPermutation.Represents ((p.layout i).child (2*2^k)) t.val.memory
      (p.data i) (ChildPermutation.finalOutputs (k+1) (p.data i)) at rep
    rw [hw]
    exact rep
  have hh := Step.cost_bound (values p.initial processed) k p.B p.B_lower (p.count processed hi)
    (p.width processed hi) (p.words processed hi)
  rw [p.count processed hi] at hh
  refine ⟨steps,t,he,hcost.trans hh,?_,ft.tapes 831 (by omega) (by omega) (by decide) (by decide)⟩
  refine ⟨?_,zt,t839,p.inputs_preserved i _ _ mf hs.inputs,p.done_preserved i _ _ mf hs.done newOutput,
    hs.frame.trans (Frame.of_step ft),p.memory_step processed _ _ _ hs.memory mf⟩
  simpa only [values_next] using bt

theorem State.initial {k : ℕ} (p : Plan k) (s : Store)
    (hb : NatAssign.Bank Division.ids p.initial s.val) (hz : PrivateVisit.Clean s)
    (h839 : Blank s.val 839) (hi : p.Inputs s.val.memory) : State p 0 s.val s :=
  ⟨hb,hz,h839,hi,fun _ h => by omega,Frame.refl _,Memory.Frame.refl _ _ _⟩

#print axioms State.counter
#print axioms State.step
end Maxwell.Cost.RoutingPorts.Complete.Tree.Level
