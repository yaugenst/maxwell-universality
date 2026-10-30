import Maxwell.Continuum.SourceRoutingAssemblyLevelPlan
import Maxwell.Continuum.SourceRoutingLevelState

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyLevel
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def bodyCost (k B : ℕ) : ℕ := 2^120*(B+2)^2+
  2^45*(2*2^k+1)*(AssemblyDescriptor.wordBound B+2)^2+
  3000*8^2*(AssemblyDescriptor.wordBound B+2)^2

structure State {rows columns depth : ℕ} (p : Plan rows columns depth) (processed : ℕ)
    (start : BitRAMState) (s : Store) : Prop where
  bank : NatAssign.Bank Division.ids (values p.initial processed) s.val
  clean : PrivateVisit.Clean s
  scratch : Blank s.val 839
  inputs : p.Inputs processed s.val.memory
  done : p.Done processed s.val.memory
  frame : Level.Frame start s.val
  memory : Memory.Frame (block p.heap p.rootCount p.rootWidth (2^depth-1))
    (processed*stride p.rootCount p.rootWidth) start.memory s.val.memory

theorem State.transfer {rows columns depth : ℕ} {p : Plan rows columns depth} {processed : ℕ}
    {start : BitRAMState} {s t : Store} (hs : State p processed start s)
    (keep : ∀i,i≠831→t.val.tapes i=s.val.tapes i) (hm : t.val.memory=s.val.memory)
    (hf : Level.Frame s.val t.val) : State p processed start t := by
  refine ⟨?_,?_,RationalAccumulator.blank_of_eq (keep 839 (by decide)) hs.scratch,?_,?_,hs.frame.trans hf,?_⟩
  · intro i hi
    apply RationalAccumulator.word_of_eq (keep i ?_) (hs.bank i hi)
    intro he;subst i;exact (show (831 : ℕ)∉Division.ids by decide) hi
  · apply (Workspace.clean_iff t).mpr
    intro i hi
    apply RationalAccumulator.blank_of_eq (keep i ?_) ((Workspace.clean_iff s).mp hs.clean i hi)
    intro he;subst i;exact (show (831 : ℕ)∉Workspace.ids by decide) hi
  · simpa only [hm] using hs.inputs
  · simpa only [hm] using hs.done
  · simpa only [hm] using hs.memory

theorem State.counter {rows columns depth : ℕ} {p : Plan rows columns depth} {processed : ℕ}
    {start : BitRAMState} {s t : Store} (hs : State p processed start s)
    (hf : CountedShifted.Frame 831 s t) : State p processed start t :=
  hs.transfer hf.2.2.2.2.2.1 hf.2.2.1 (Level.Frame.of_counter hf)

theorem State.clear {rows columns depth : ℕ} {p : Plan rows columns depth} {processed : ℕ}
    {start : BitRAMState} {s t : Store} (hs : State p processed start s)
    (hf : BinaryPrecision.Frame {831} s.val t.val) : State p processed start t :=
  hs.transfer (fun i hi => hf.tapes i (by simpa using hi)) hf.memory
    ⟨hf.inputHead,hf.randomCursor,hf.output,fun i _ _ _ _ hi => hf.tapes i (by simpa using hi)⟩

theorem State.step {rows columns depth : ℕ} (p : Plan rows columns depth) (processed : ℕ)
    (hi : processed<2^depth) (input : List Bool) (tape : ℕ→Bool)
    (start : BitRAMState) (s : Store) (hs : State p processed start s) :
    ∃steps t,Executes input tape AssemblyStep.code steps s t ∧
      steps ≤ bodyCost (columns+rows) (uniformWidth p.L) ∧ State p (processed+1) start t ∧
      t.val.tapes 831=s.val.tapes 831 := by
  let i : Fin (2^depth):=⟨processed,hi⟩
  have coords:=coordinates p.initial p.heap p.rootCount p.rootWidth depth (columns+rows) p.coordinates processed
  have words:=values_simple_width p.initial processed p.L p.L_lower p.words
    ((Maxwell.Continuum.RationalWords.bits_mono (Nat.le_of_lt hi)).trans p.nodes_width)
  have hz : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,values p.initial processed j=0 := by
    intro j hj
    have disjoint : Disjoint Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts writes := by decide
    rw [values_other p.initial processed j (Finset.disjoint_left.mp disjoint hj)]
    exact p.zero j hj
  have data:=hs.inputs i le_rfl
  obtain ⟨steps,t,he,hcost,bt,zt,t839,result,ft,mt⟩:=AssemblyStep.executes (values p.initial processed)
    p.heap p.rootCount p.rootWidth depth rows columns (uniformWidth p.L) i coords p.count_fits p.width_fits
    (by dsimp only [uniformWidth];omega) hz words (p.target i) input tape s hs.bank hs.clean hs.scratch data.1 data.2
  have finalLabels:=(labelsAt_succ p.heap p.rootCount p.rootWidth (levelNode depth i)
    rows columns (p.target i) t.val.memory).mpr result
  have mnext : Memory.Frame (block p.heap p.rootCount p.rootWidth (2^depth-1)+
      processed*stride p.rootCount p.rootWidth) (stride p.rootCount p.rootWidth) s.val.memory t.val.memory := by
    simpa only [block,levelNode,Nat.add_mul,Nat.add_assoc] using mt
  refine ⟨steps,t,he,?_,⟨?_,zt,t839,p.inputs_preserved i _ _ mt hs.inputs,
    p.done_preserved i _ _ mt hs.done finalLabels,hs.frame.trans (Level.Frame.of_step ft),?_⟩,
    ft.tapes 831 (by omega) (by omega) (by decide) (by decide)⟩
  · change steps ≤ AssemblyStep.cost (values p.initial processed) (uniformWidth p.L) at hcost
    simpa only [AssemblyStep.cost,coords.count,bodyCost] using hcost
  · simpa only [values_next] using bt
  · simpa only [Nat.add_mul,Nat.one_mul] using Level.memory_append hs.memory mnext

#print axioms State.step
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyLevel
