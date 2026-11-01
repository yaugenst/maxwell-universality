import Maxwell.Continuum.SourceRoutingCountedGeometry
import Maxwell.Continuum.ParameterSourcePrepare

/-! Source-driven preparation of every operand for parameter selection.
The source graph, routing histories, geometry, and well count are executed
before these operands are copied and computed. -/
noncomputable section
namespace Maxwell.Continuum.Parameters.SourceExecution
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RoutingPorts.Complete
open Maxwell.Logical Maxwell.Composition
open RationalAccumulator (Word Blank)
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

def values (κ η e : ℕ) (S : Source.SparseSystem) (precision : ℕ) : ℕ→ℕ :=
  SourcePrepare.values κ η e S.n S.nnz (sourceCircuit S precision).size
    (SourcePhase.side S precision) (Fintype.card (SourceDecoration.Vertex S precision))
def code (κ η e : ℕ) : Code := .seq CountedGeometry.code (SourcePrepare.code κ η e)
def work : Finset ℕ := CountedGeometry.work∪SourcePrepare.work
def cost (κ η e : ℕ) (S : Source.SparseSystem) (precision : ℕ)
    (room : SourceGraph.Positive.dimension S precision<2^SourceGraph.Positive.width S precision) : ℕ :=
  CountedGeometry.cost S precision room+SourcePrepare.cost κ η e S.n S.nnz
    (sourceCircuit S precision).size (SourcePhase.side S precision) (Fintype.card (SourceDecoration.Vertex S precision))

structure Result (κ η e : ℕ) (S : Source.SparseSystem) (precision : ℕ) (s : Store) : Prop where
  bank : NatAssign.Bank SourcePrepare.ports (values κ η e S precision) s.val
  scratch : NatAssign.Scratch s.val
  saved : ∃previous : Store,CountedGeometry.Result S precision previous ∧
    BinaryPrecision.Frame SourcePrepare.work previous.val s.val

theorem executes (κ η e : ℕ) (S : Source.SparseSystem) (precision : ℕ) (hm : 2≤S.nnz)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : SourceGraph.Incidence.Result S precision s) :
    ∃steps t,Executes input tape (code κ η e) steps s t ∧ steps≤cost κ η e S precision hs.room ∧
      Result κ η e S precision t ∧ ArchiveFrame work s.val t.val ∧
      (∀address,address<(SourcePlan.treeLayout S precision).forward→t.val.memory address=s.val.memory address) := by
  obtain ⟨c₀,a,e₀,h₀,ra,f₀,m₀⟩:=CountedGeometry.executes S precision hm input tape s hs
  have fresh : ∀i∈SourceLogMachine.ids,Blank a.val i := by
    intro i hi
    apply ra.fresh
    simp only [SourceLogMachine.ids,SourceBudgetMachine.ids,SourceBudgetMachine.extra,
      SourceBudgetMachine.outputs,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
    omega
  obtain ⟨c₁,t,e₁,h₁,bt,zt,f₁⟩:=SourcePrepare.executes κ η e S.n S.nnz
    (sourceCircuit S precision).size (SourcePhase.side S precision)
    (Fintype.card (SourceDecoration.Vertex S precision)) input tape a
    ra.data.numeric.dimension ra.data.numeric.count ra.data.circuitSize ra.sideWord ra.sitesWord
    fresh (GeometryArithmetic.scratch ra.ready)
  refine ⟨c₀+c₁,t,e₀.seq e₁,Nat.add_le_add h₀ h₁,⟨bt,zt,⟨a,ra,f₁⟩⟩,
    (f₀.mono Finset.subset_union_left).trans ((ArchiveFrame.of_binary f₁).mono Finset.subset_union_right),?_⟩
  intro address ha
  rw [f₁.memory]
  exact m₀ address ha

theorem Result.fresh {κ η e : ℕ} {S : Source.SparseSystem} {precision : ℕ} {s : Store}
    (h : Result κ η e S precision s) (i : ℕ) (lo : 1261 ≤ i) (outside : i∉SourcePrepare.work) :
    Blank s.val i := by
  obtain ⟨previous,old,frame⟩:=h.saved
  exact RationalAccumulator.blank_of_eq (frame.tapes i outside) (old.fresh i lo)

theorem Result.data {κ η e : ℕ} {S : Source.SparseSystem} {precision : ℕ} {s : Store}
    (h : Result κ η e S precision s) : SourceGraph.Retain.Data S precision s.val := by
  obtain ⟨previous,old,frame⟩:=h.saved
  apply old.data.transport
  intro i lo hi
  apply frame.tapes
  have disjoint : Disjoint (Finset.Icc 500 509) SourcePrepare.work := by decide +kernel
  exact Finset.disjoint_left.mp disjoint (Finset.mem_Icc.mpr ⟨lo,hi⟩)

#print axioms executes
#print axioms Result.data
end Maxwell.Continuum.Parameters.SourceExecution
