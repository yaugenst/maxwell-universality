import Maxwell.Continuum.SourceRoutingSourceTarget

/-! The source program's arithmetic ports are the ports of the declared
indexed graph. Finite casts preserve the deterministic incidence ordering. -/

namespace Maxwell.Logical.Routing.IncidenceRanks
theorem ranks_cast {v w k l : ℕ} (hv : v=w) (hk : k=l)
    (f : Fin k→Fin v) (hf : DegreeBound f) (g : Fin l→Fin w) (hg : DegreeBound g)
    (he : ∀i,g (Fin.cast hk i)=Fin.cast hv (f i)) (i : Fin k) :
    (ranks g hg).get (Fin.cast hk i)=(ranks f hf).get i := by
  subst w
  subst l
  have eq : g=f := by funext j; simpa using he j
  subst g
  rfl
end Maxwell.Logical.Routing.IncidenceRanks

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePlan
open Maxwell.Logical Maxwell.Logical.Routing Maxwell.Logical.Routing.Gluing
open SourceGraph.Positive
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

abbrev indexedVertices (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  (sourceCircuit S p).size+(sourceCircuit S p).size+(sourceSquareEntries S p).length
abbrev indexedEdges (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  (sourceSquareEntries S p).length+(sourceSquareEntries S p).length
abbrev indexedIncidences (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  Fintype.card (Fin (indexedEdges S p)×Bool)

theorem half_indexed (S : Source.SparseSystem) (p : ℕ) :
    half S p=portHalfSide (indexedVertices S p) :=
  congrArg portHalfSide (SourceGraph.Incidence.vertex_count S p).symm

theorem rank_indexed (S : Source.SparseSystem) (p : ℕ) (i : Fin (indexedIncidences S p)) :
    rank S p (Fin.cast (SourceGraph.Incidence.incidence_count S p) i)=
      (IncidenceRanks.ranks (Composition.SourceRouting.flatEndpoint S p)
        (Composition.SourceRouting.flatEndpoint_degree S p)).get i := by
  exact IncidenceRanks.ranks_cast (SourceGraph.Incidence.vertex_count S p)
    (SourceGraph.Incidence.incidence_count S p) _ _ _ _
    (fun j => by simp [SourceGraph.Incidence.endpoint]) i

def indexedSource (S : Source.SparseSystem) (p : ℕ) (i : Fin (indexedIncidences S p)) :
    Fin ((2*portHalfSide (indexedVertices S p))*(2*portHalfSide (indexedVertices S p))) :=
  let data:=Composition.SourceRouting.indexedData S p
  let pair:=(incidenceIndex (indexedEdges S p)).symm i
  finProdFinEquiv (tilePort (data.tile (data.endpoint pair.1 pair.2)) (data.arm pair.1 pair.2))

def indexedTarget (S : Source.SparseSystem) (p : ℕ) (i : Fin (indexedIncidences S p)) :
    Fin ((2*portHalfSide (indexedVertices S p))*(2*portHalfSide (indexedVertices S p))) :=
  let data:=Composition.SourceRouting.indexedData S p
  let pair:=(incidenceIndex (indexedEdges S p)).symm i
  finProdFinEquiv (pairPort (data.pair pair.1) pair.2)

theorem source_indexed (S : Source.SparseSystem) (p : ℕ) (i : Fin (indexedIncidences S p)) :
    (source S p (Fin.cast (SourceGraph.Incidence.incidence_count S p) i)).val=
      (indexedSource S p i).val := by
  calc
    _ = PortIndices.sourceIndex (half S p)
        (SourceGraph.Incidence.endpoint S p (Fin.cast (SourceGraph.Incidence.incidence_count S p) i)).val
        (rank S p (Fin.cast (SourceGraph.Incidence.incidence_count S p) i)).val :=
      PortIndices.sourcePort_value _ _ _ _ _
    _ = _ := ?_
  rw [half_indexed,rank_indexed]
  dsimp only [indexedSource,Composition.SourceRouting.indexedData,indexedGraphData]
  rw [PortIndices.source_exact]
  simp [SourceGraph.Incidence.endpoint,Fin.cast,indexedEdges,
    Composition.SourceRouting.flatEndpoint]

theorem target_indexed (S : Source.SparseSystem) (p : ℕ) (i : Fin (indexedIncidences S p)) :
    (target S p (Fin.cast (SourceGraph.Incidence.incidence_count S p) i)).val=
      (indexedTarget S p i).val := by
  change PortIndices.targetIndex (half S p) i.val=(indexedTarget S p i).val
  dsimp only [indexedTarget,Composition.SourceRouting.indexedData,indexedGraphData]
  rw [PortIndices.pair_exact,half_indexed]
  congr 1
  exact ((PortIndices.incidenceIndex_value ((incidenceIndex (indexedEdges S p)).symm i).1
    ((incidenceIndex (indexedEdges S p)).symm i).2).symm.trans
    (congrArg Fin.val ((incidenceIndex (indexedEdges S p)).apply_symm_apply i))).symm

#print axioms source_indexed
#print axioms target_indexed
end Maxwell.Cost.RoutingPorts.Complete.SourcePlan
