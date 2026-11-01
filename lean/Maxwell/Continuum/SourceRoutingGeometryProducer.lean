import Maxwell.Continuum.SourceRoutingGeometryInitialize
import Maxwell.Continuum.SourceRoutingGeometryCapacity

/-! From the three computed source histories to the complete packed source
geometry. Initialization and traversal are one fixed charged program. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryProducer
open Structured Maxwell.Logical Maxwell.Logical.Routing Maxwell.Composition
open SourceDecorationEnumeration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

abbrev vertices (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  (sourceCircuit S p).size+(sourceCircuit S p).size+(sourceSquareEntries S p).length
abbrev edges (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  (sourceSquareEntries S p).length+(sourceSquareEntries S p).length
abbrev side (S : Source.SparseSystem) (p : ℕ) : ℕ := 2*portHalfSide (vertices S p)
def code : Code:=.seq GeometryStartup.code GeometryEmission.code
def work : Finset ℕ:=GeometryStartup.work∪GeometryEmission.work
def price (S : Source.SparseSystem) (precision : ℕ) (h : GeometryHistory.Plan (side S precision))
    (backward : ℕ) (start : h.base=backward+12*h.stride) : ℕ :=
  GeometryStartup.cost h backward+
    GeometryEmission.price (GeometryStartup.plan h backward start)
      (GeometryEmission.capacity (side S precision) (vertices S precision) (edges S precision))
      (vertices S precision) (edges S precision) ((sourceCircuit S precision).size+(sourceCircuit S precision).size)

theorem target_fits {q : ℕ} (h : GeometryHistory.Plan q) (target : Equiv.Perm (Port q)) :
    GeometrySort.Fits h.width (SortArrays.targetArray target) := by
  intro i
  simp only [SortArrays.targetArray,SortArrays.get_ofFn]
  exact Maxwell.Continuum.RationalWords.bits_mono (show (target (finProdFinEquiv.symm i)).1.val≤q*q by
    have small:=(target (finProdFinEquiv.symm i)).1.isLt
    have positive:=h.positive
    nlinarith)

theorem executes (S : Source.SparseSystem) (precision : ℕ) (h : GeometryHistory.Plan (side S precision))
    (backward : ℕ) (start : h.base=backward+12*h.stride)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (runtime : GeometryHistory.Runtime h.following.following
      (PhaseKeys.last (SourceRouting.indexedData S precision).colors) (2*side S precision) s)
    (backwardWord : Word s.val 717 backward)
    (first : GeometryHistory.Stored h (PhaseKeys.first (SourceRouting.indexedData S precision).colors)
      (2*side S precision) s.val.memory)
    (second : GeometryHistory.Stored h.following (PhaseKeys.middle (SourceRouting.indexedData S precision).colors)
      (2*side S precision) s.val.memory)
    (inverse : BitArray.Represents s.val.memory backward h.width
      (IncidenceEncoding.words h.width (GeometryPhase.targets (SourceRouting.indexedData S precision).target.symm)))
    (fresh : ∀i∈GeometryStartup.freshPorts,Blank s.val i)
    (totalWord : Word s.val 141 (vertices S precision))
    (leftWord : Word s.val 154 ((sourceCircuit S precision).size+(sourceCircuit S precision).size))
    (edgeWord : Word s.val 153 (edges S precision)) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤price S precision h backward start ∧
      GeometryEmission.State (SourceRouting.indexedData S precision) (GeometryStartup.plan h backward start)
        (packedLength (SourceEmission.geometry S precision)) (edges S precision) t ∧
      Blank t.val 1258 ∧
      StoredGeometry (SourceEmission.geometry S precision) (GeometryStartup.outputBase h)
        (GeometryStartup.outputWidth h) t.val.memory ∧
      Represents S precision (SourceEmission.geometry S precision) ∧ ArchiveFrame work s.val t.val ∧
      Tree.Memory.Frame (GeometryStartup.outputBase h)
        (GeometryEmission.capacity (side S precision) (vertices S precision) (edges S precision)*
          GeometryStartup.outputWidth h) s.val.memory t.val.memory := by
  obtain ⟨c₀,a,e₀,h₀,sa,ca,f₀⟩:=GeometryStartup.prepares (SourceRouting.indexedData S precision)
    h backward start input tape s runtime backwardWord first second inverse fresh
  have room:=GeometryEmission.capacity_room (SourceRouting.indexedData S precision) h.positive
    (SourceEmission.geometry S precision) (fun _=>by simp only [SourceEmission.geometry,SortArrays.get_ofFn])
  obtain ⟨c₁,t,e₁,h₁,st,ct,stored,represented,f₁,m₁⟩:=GeometryEmission.source_executes S precision
    (GeometryStartup.plan h backward start)
    (GeometryEmission.capacity (side S precision) (vertices S precision) (edges S precision))
    (target_fits h _) (target_fits h _) (target_fits h _) room input tape a sa ca
    (RationalAccumulator.word_of_eq (f₀.tapes 141 (by decide)) totalWord)
    (RationalAccumulator.word_of_eq (f₀.tapes 154 (by decide)) leftWord)
    (RationalAccumulator.word_of_eq (f₀.tapes 153 (by decide)) edgeWord)
  refine ⟨c₀+c₁,t,e₀.seq e₁,Nat.add_le_add h₀ h₁,st,ct,stored,represented,
    ((ArchiveFrame.of_binary f₀).mono Finset.subset_union_left).trans (f₁.mono Finset.subset_union_right),?_⟩
  rw [f₀.memory] at m₁
  exact m₁

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryProducer
