import Maxwell.Continuum.SourceWellDegrees
import Maxwell.Cost.SourceGraph.Incidence
import Maxwell.Cost.PositiveGraph.Invariant

/-! Concrete original-diagonal and degree tables retained by source routing.
The two fixed-width arrays decode to the actual PhysicalDiagonal inputs. -/
noncomputable section
namespace Maxwell.Continuum.SourceStrengthTables
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition
open Maxwell.Logical Maxwell.Logical.Routing
open SourceGraph.Positive
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

variable (S : Source.SparseSystem) (p : ℕ)

def vertexIndex (v : SourcePositive.Vertex S p) : Fin (2*dimension S p+count S p) :=
  Fin.cast (SourceGraph.Incidence.vertex_count S p) (SourceEnumeration.vertexEquiv S p v)

def endpointIndex : Fin (4*count S p) ≃ SourceRouting.Edge S p×Bool :=
  ((finCongr (SourceGraph.Incidence.incidence_count S p).symm).trans
    (Gluing.incidenceIndex ((sourceSquareEntries S p).length+(sourceSquareEntries S p).length)).symm).trans
    ((SourceEnumeration.positiveEdgeEquiv S p).symm.prodCongr (Equiv.refl Bool))

theorem endpointIndex_correct (i : Fin (4*count S p)) :
    SourceGraph.Incidence.endpoint S p i=vertexIndex S p
      ((SourcePositive.graph S p).endpoint (endpointIndex S p i).1 (endpointIndex S p i).2) := by
  simp only [SourceGraph.Incidence.endpoint,SourceRouting.flatEndpoint,SourceCached.positiveEndpoint_eq,
    SourceEnumeration.positiveEndpoint_correct,vertexIndex,endpointIndex,Equiv.trans_apply,
    Equiv.prodCongr_apply,SignedIncidence.endpoint]
  rfl

theorem counter_eq_degree (v : SourcePositive.Vertex S p) :
    (IncidenceRanks.run (SourceGraph.Incidence.endpoint S p) (4*count S p) le_rfl).counters.get
      (vertexIndex S p v)=PhysicalDiagonal.degree S p (.inl v) := by
  rw [IncidenceRanks.counters_eq,IncidenceRanks.priorCount,IncidenceRanks.prior]
  have he := (endpointIndex S p).subtypeEquiv
    (p := fun i=>i.val<4*count S p ∧ SourceGraph.Incidence.endpoint S p i=vertexIndex S p v)
    (q := fun q=>(SourcePositive.graph S p).endpoint q.1 q.2=v) (by
      intro i
      rw [endpointIndex_correct]
      simp only [i.isLt,true_and,vertexIndex,Fin.cast_inj,Equiv.apply_eq_iff_eq])
  have hc := Fintype.card_congr he
  rw [Fintype.card_subtype,Fintype.card_subtype] at hc
  exact hc.trans (PhysicalDiagonal.degree_original S p v).symm

structure Represents (memory : ℕ→Bool) : Prop where
  diagonal : BitArray.Represents memory (base S p) 4 (PositiveGraph.Invariant.sourceDiagonalWords S p)
  counter : BitArray.Represents memory (4*count S p*(width S p+3)) 2
    (IncidenceEncoding.words 2
      (IncidenceRanks.run (SourceGraph.Incidence.endpoint S p) (4*count S p) le_rfl).counters)

theorem of_result {s : Store} (h : SourceGraph.Incidence.Result S p s) : Represents S p s.val.memory :=
  ⟨h.diagonal,h.incidence.counters⟩

theorem Represents.read_degree {memory : ℕ→Bool} (h : Represents S p memory)
    (v : SourcePositive.Vertex S p) :
    addressValue (MemoryWord.readBits memory
      (4*count S p*(width S p+3)+(vertexIndex S p v).val*2) 2)=
      PhysicalDiagonal.degree S p (.inl v) := by
  rw [h.counter.read,IncidenceEncoding.words_value]
  · exact counter_eq_degree S p v
  · have h3 := IncidenceEncoding.run_counters_le_three (SourceGraph.Incidence.endpoint S p)
      (SourceGraph.Incidence.endpoint_degree S p) (4*count S p) le_rfl (vertexIndex S p v)
    omega

theorem Represents.read_diagonal {memory : ℕ→Bool} (h : Represents S p memory)
    (v : SourcePositive.Vertex S p) :
    ((addressValue (MemoryWord.readBits memory (base S p+(vertexIndex S p v).val*4) 4):ℚ)-8)/2=
      SourceVertexList.diagonal S p (.inl v) := by
  erw [h.diagonal.read]
  have hg : (PositiveGraph.Invariant.sourceDiagonalWords S p).get (vertexIndex S p v)=
      FixedWidth.bits 4 (PositiveGraph.diagonalCode
        ((PositiveScatter.numerator S p).get (SourceEnumeration.vertexEquiv S p v))).bits := by
    simp [PositiveGraph.Invariant.sourceDiagonalWords,vertexIndex,Vector.get,Fin.cast]
  rw [hg,FixedWidth.bits_value, addressValue_bits]
  · have hd := PositiveGraph.source_diagonal_code S p (SourceEnumeration.vertexEquiv S p v)
    push_cast at hd
    simpa only [SourceVertexList.diagonal,SourceEmission.geometry,PositiveScatter.diagonal_get] using hd
  · rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (PositiveGraph.diagonalCode_lt _)

#print axioms counter_eq_degree
#print axioms Represents.read_diagonal
end Maxwell.Continuum.SourceStrengthTables
