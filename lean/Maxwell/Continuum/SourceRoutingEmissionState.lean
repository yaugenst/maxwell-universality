import Maxwell.Continuum.SourceRoutingPackedEdge
import Maxwell.Continuum.SourceRoutingEdgeSelect
import Maxwell.Cost.PhysicalEmit.Increment

/-! One state boundary for the packed geometry producer. The stored routing
histories and inverse permutation are retained across every emitted record. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
open Structured GeometryArithmetic GeometryPath Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

structure Plan (q : ℕ) where
  path : GeometryPathPhase.Plan q
  secondBefore : path.history.following.slab (2*q+1) ≤ path.base
  thirdBefore : path.history.following.following.slab (2*q+1) ≤ path.base
  backward : ℕ
  backwardBefore : backward+q*q*path.history.width ≤ path.base

def stepWork : Finset ℕ := {1257}∪packedEdgeWork
def work : Finset ℕ := {1258}∪stepWork

structure Archive {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (p : Plan (2*half)) (s : BitRAMState) : Prop where
  metadata : GeometrySort.Metadata (p.path.history.layer 0) s
  output : OutputMetadata p.path.width p.path.base p.path.clock s
  backwardWord : Word s 1260 p.backward
  first : GeometryHistory.Stored p.path.history (PhaseKeys.first data.colors) (2*(2*half)) s.memory
  second : GeometryHistory.Stored p.path.history.following (PhaseKeys.middle data.colors) (2*(2*half)) s.memory
  third : GeometryHistory.Stored p.path.history.following.following (PhaseKeys.last data.colors) (2*(2*half)) s.memory
  backwardStored : BitArray.Represents s.memory p.backward p.path.history.width
    (IncidenceEncoding.words p.path.history.width (GeometryPhase.targets data.target.symm))

theorem Archive.frame {V E : Type*} {half : ℕ} {data : Gluing.Data V E half}
    {p : Plan (2*half)} {s t : BitRAMState} (a : Archive data p s) (n : ℕ)
    (frame : ArchiveFrame work s t) (memory : Tree.Memory.Frame p.path.base (n*p.path.width) s.memory t.memory) :
    Archive data p t := by
  refine ⟨a.metadata.frame frame (by decide),
    ⟨RationalAccumulator.word_of_eq (frame.tapes 1250 (by decide) (by decide)) a.output.wordWidth,
      RationalAccumulator.word_of_eq (frame.tapes 1252 (by decide) (by decide)) a.output.baseWord,
      BankArray.word_of_eq (frame.tapes 1251 (by decide) (by decide)) a.output.clockWord⟩,
    RationalAccumulator.word_of_eq (frame.tapes 1260 (by decide) (by decide)) a.backwardWord,
    p.path.history_frame _ n a.first memory,
    (p.path.following p.secondBefore).history_frame _ n a.second memory,
    ((p.path.following p.secondBefore).following p.thirdBefore).history_frame _ n a.third memory,
    memory.represents (Or.inl p.backwardBefore) a.backwardStored⟩

structure State {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (p : Plan (2*half)) (cursor index : ℕ) (s : Store) : Prop where
  bank : ∃port : Fin ((2*half)*(2*half)),
    NatAssign.Bank ids (GeometrySort.seed (p.path.history.layer 0) 1 port.val) s.val
  ready : GeometryArray.Ready s.val
  privateBlank : Blank s.val 1249
  archive : Archive data p s.val
  levelWord : Word s.val 1255 0
  cursorWord : Word s.val 1253 cursor
  indexWord : Word s.val 1257 index
  counterBlank : Blank s.val 1242
  savedBlank : Blank s.val 1256

theorem State.control_frame {V E : Type*} {half : ℕ} {data : Gluing.Data V E half}
    {p : Plan (2*half)} {cursor index next : ℕ} {s t : Store} (state : State data p cursor index s)
    (memory : t.val.memory=s.val.memory)
    (keep : ∀j,j≠1257→j≠1258→t.val.tapes j=s.val.tapes j)
    (indexWord : Word t.val 1257 next) : State data p cursor next t := by
  obtain ⟨port,bank⟩:=state.bank
  refine ⟨⟨port,?_⟩,state.ready.of_tapes (fun j hj => keep j (by omega) (by omega)),
    RationalAccumulator.blank_of_eq (keep 1249 (by decide) (by decide)) state.privateBlank,?_,
    RationalAccumulator.word_of_eq (keep 1255 (by decide) (by decide)) state.levelWord,
    RationalAccumulator.word_of_eq (keep 1253 (by decide) (by decide)) state.cursorWord,indexWord,
    RationalAccumulator.blank_of_eq (keep 1242 (by decide) (by decide)) state.counterBlank,
    RationalAccumulator.blank_of_eq (keep 1256 (by decide) (by decide)) state.savedBlank⟩
  · intro j hj
    have ne : j≠1257 ∧ j≠1258 := by
      simp only [ids,controls,Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
        Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hj
      omega
    exact RationalAccumulator.word_of_eq (keep j ne.1 ne.2) (bank j hj)
  · refine ⟨⟨RationalAccumulator.word_of_eq (keep 711 (by decide) (by decide)) state.archive.metadata.width,
      BankArray.word_of_eq (keep 718 (by decide) (by decide)) state.archive.metadata.clock⟩,
      ⟨RationalAccumulator.word_of_eq (keep 1250 (by decide) (by decide)) state.archive.output.wordWidth,
        RationalAccumulator.word_of_eq (keep 1252 (by decide) (by decide)) state.archive.output.baseWord,
        BankArray.word_of_eq (keep 1251 (by decide) (by decide)) state.archive.output.clockWord⟩,
      RationalAccumulator.word_of_eq (keep 1260 (by decide) (by decide)) state.archive.backwardWord,
      ?_,?_,?_,?_⟩
    all_goals rw [memory]
    · exact state.archive.first
    · exact state.archive.second
    · exact state.archive.third
    · exact state.archive.backwardStored

theorem State.counted {V E : Type*} {half : ℕ} {data : Gluing.Data V E half}
    {p : Plan (2*half)} {cursor index : ℕ} {s t : Store} (state : State data p cursor index s)
    (frame : CountedShifted.Frame 1258 s t) : State data p cursor index t :=
  state.control_frame frame.2.2.1 (fun j _ hj => frame.2.2.2.2.2.1 j hj)
    (RationalAccumulator.word_of_eq (frame.2.2.2.2.2.1 1257 (by decide)) state.indexWord)

theorem State.increment {V E : Type*} {half : ℕ} {data : Gluing.Data V E half}
    {p : Plan (2*half)} {cursor index : ℕ} {s : Store} (state : State data p cursor index s)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃steps t,Executes input tape (PhysicalEmit.incrementCode 1257) steps s t ∧
      steps ≤ 12*index.bits.length+18 ∧ State data p cursor (index+1) t ∧
      t.val.memory=s.val.memory ∧ ArchiveFrame {1257} s.val t.val := by
  obtain ⟨steps,t,hc,he,word,frame⟩:=PhysicalEmit.increment 1257 index input tape s state.indexWord
  exact ⟨steps,t,he,hc,state.control_frame frame.memory (fun j hj _ => frame.tapes j (by simpa using hj)) word,
    frame.memory,⟨frame.inputHead,frame.randomCursor,frame.output,fun j _ hj => frame.tapes j hj⟩⟩

#print axioms State.increment
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
