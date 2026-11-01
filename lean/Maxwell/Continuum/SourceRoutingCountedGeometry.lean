import Maxwell.Continuum.SourceRoutingSourceGeometry
import Maxwell.Continuum.ParameterGeometryCountMachine

/-! The complete geometry computation exposes its actual well count and
retained source words to the parameter search. -/
noncomputable section
namespace Maxwell.Cost.RoutingPorts.Complete.CountedGeometry
open Structured Maxwell.Logical Maxwell.Logical.Routing Maxwell.Composition
open SourceDecorationEnumeration Maxwell.Continuum.Parameters
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

def countWidth (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  ((SourceGeometry.history S p).layer 0).bound 1+
    (packedLength (SourceEmission.geometry S p)).bits.length+
    (GeometryProducer.vertices S p).bits.length+(GeometryProducer.edges S p).bits.length+4
def code : Code := .seq SourceGeometry.code GeometryCountMachine.code
def work : Finset ℕ := SourceGeometry.work∪GeometryArithmetic.work
def cost (S : Source.SparseSystem) (p : ℕ)
    (room : SourceGraph.Positive.dimension S p<2^SourceGraph.Positive.width S p) : ℕ :=
  SourceGeometry.cost S p room+2^130*(countWidth S p+2)^2

structure Result (S : Source.SparseSystem) (p : ℕ) (s : Store) : Prop where
  ready : GeometryArray.Ready s.val
  privateBlank : Blank s.val 1249
  stored : StoredGeometry (SourceEmission.geometry S p) (GeometryStartup.outputBase (SourceGeometry.history S p))
    (GeometryStartup.outputWidth (SourceGeometry.history S p)) s.val.memory
  represented : Represents S p (SourceEmission.geometry S p)
  output : GeometryPath.OutputMetadata (GeometryStartup.outputWidth (SourceGeometry.history S p))
    (GeometryStartup.outputBase (SourceGeometry.history S p)) (GeometryStartup.outputClock (SourceGeometry.history S p)) s.val
  sideWord : Word s.val 1200 (SourcePhase.side S p)
  sitesWord : Word s.val 1209 (Fintype.card (SourceDecoration.Vertex S p))
  cursorWord : Word s.val 1253 (packedLength (SourceEmission.geometry S p))
  data : SourceGraph.Retain.Data S p s.val
  numeric : PositiveGraph.Metadata.Numeric (SourceGraph.Positive.width S p)
    (SourceGraph.Positive.dimension S p) (SourceGraph.Positive.count S p) s.val
  fresh : ∀i,1261 ≤ i→Blank s.val i

theorem executes (S : Source.SparseSystem) (p : ℕ) (hm : 2≤S.nnz)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : SourceGraph.Incidence.Result S p s) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost S p hs.room ∧ Result S p t ∧
      ArchiveFrame work s.val t.val ∧
      (∀address,address<(SourcePlan.treeLayout S p).forward→t.val.memory address=s.val.memory address) := by
  obtain ⟨c₀,a,e₀,h₀,state,_,stored,represented,f₀,m₀⟩:=SourceGeometry.executes S p hm input tape s hs
  obtain ⟨port,bank⟩:=state.bank
  let seed:=GeometrySort.seed ((SourceGeometry.history S p).layer 0) 1 port.val
  have numeric:=SourceGeometry.numeric hs f₀
  have bw:=GeometrySort.seed_width ((SourceGeometry.history S p).layer 0) 1 port.val port.isLt.le
  have identity:=siteCount_cursor_identity (SourceEmission.geometry S p) represented.path_length_two
  obtain ⟨c₁,t,e₁,h₁,bt,zt,t1249,f₁⟩:=GeometryCountMachine.executes seed
    (packedLength (SourceEmission.geometry S p)) (GeometryProducer.vertices S p) (GeometryProducer.edges S p)
    (countWidth S p) (by unfold countWidth;omega)
    (fun i hi=>(bw i hi).trans (by unfold countWidth;omega))
    (by unfold countWidth;omega) (by unfold countWidth;omega) (by unfold countWidth;omega)
    (by unfold GeometryProducer.vertices GeometryProducer.edges;omega)
    (GeometrySort.seed_zero _ _ _) input tape a bank state.ready state.privateBlank state.cursorWord
    (by simpa only [SourceGraph.Positive.dimension,SourceGraph.Positive.count,GeometryProducer.vertices,Nat.two_mul]
      using numeric.vertices)
    (by simpa only [SourceGraph.Positive.count,GeometryProducer.edges,Nat.two_mul] using numeric.edges)
  have sites:=Represents.card_from_cursor S p represented
  have data:=SourceGeometry.retained hs f₀
  refine ⟨c₀+c₁,t,e₀.seq e₁,Nat.add_le_add h₀ h₁,⟨zt,t1249,?_,represented,?_,?_,?_,
    RationalAccumulator.word_of_eq (f₁.tapes 1253 (by decide)) state.cursorWord,?_,?_,?_⟩,
    (f₀.mono Finset.subset_union_left).trans ((ArchiveFrame.of_binary f₁).mono Finset.subset_union_right),?_⟩
  · rw [f₁.memory]
    exact stored
  · exact ⟨RationalAccumulator.word_of_eq (f₁.tapes 1250 (by decide)) state.archive.output.wordWidth,
      RationalAccumulator.word_of_eq (f₁.tapes 1252 (by decide)) state.archive.output.baseWord,
      BankArray.word_of_eq (f₁.tapes 1251 (by decide)) state.archive.output.clockWord⟩
  · simpa [GeometryCountMachine.output_side,seed,GeometrySort.seed] using bt 1200 (by decide)
  · simpa only [GeometryCountMachine.output_count,←sites] using bt 1209 (by decide)
  · apply data.transport
    intro i lo hi
    apply f₁.tapes
    simp only [GeometryArithmetic.work,GeometryArithmetic.ids,GeometryArithmetic.controls,
      Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
    omega
  · apply numeric.transport
    intro i lo hi _
    apply f₁.tapes
    simp only [GeometryArithmetic.work,GeometryArithmetic.ids,GeometryArithmetic.controls,
      Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
    omega
  · intro i hi
    apply RationalAccumulator.blank_of_eq (f₁.tapes i ?_) (SourceGeometry.fresh hs f₀ i hi)
    simp only [GeometryArithmetic.work,GeometryArithmetic.ids,GeometryArithmetic.controls,
      Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
    omega
  · intro address ha
    rw [f₁.memory]
    exact m₀ address ha

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.CountedGeometry
