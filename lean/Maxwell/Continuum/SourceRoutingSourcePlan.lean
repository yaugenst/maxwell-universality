import Maxwell.Continuum.SourceRoutingPermutation
import Maxwell.Continuum.SourceRoutingStartup
import Maxwell.Continuum.SourceRoutingPortInjective
import Maxwell.Cost.SourceGraph.Incidence

/-! The routing plan is determined by the source circuit and the endpoint
and incidence-rank arrays actually produced by the source frontend. -/

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePlan
open Maxwell.Logical.Routing SourceGraph.Positive
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def vertices (S : Source.SparseSystem) (p : ℕ) : ℕ := 2*dimension S p+count S p
def half (S : Source.SparseSystem) (p : ℕ) : ℕ := portHalfSide (vertices S p)
def size (S : Source.SparseSystem) (p : ℕ) : ℕ := Startup.gridSize (vertices S p)

theorem vertex_room (S : Source.SparseSystem) (p : ℕ) :
    vertices S p≤half S p*half S p := by
  rw [←pow_two,half,portHalfSide_square]
  exact Nat.le_pow_clog (by decide) _

theorem incidence_room (S : Source.SparseSystem) (p : ℕ) :
    4*count S p≤2*(half S p*(2*half S p)) := by
  have h := vertex_room S p
  unfold vertices at h
  nlinarith only [h]

theorem size_eq (S : Source.SparseSystem) (p : ℕ) :
    (2*half S p)*(2*half S p)=size S p := by
  simpa only [size,half,portHalfSide,pow_two] using (Startup.gridSize_square (vertices S p)).symm

def rank (S : Source.SparseSystem) (p : ℕ) : Fin (4*count S p)→Fin 3 :=
  (IncidenceRanks.ranks (SourceGraph.Incidence.endpoint S p)
    (SourceGraph.Incidence.endpoint_degree S p)).get
def rankValues (S : Source.SparseSystem) (p : ℕ) : Vector ℕ (4*count S p) :=
  (IncidenceRanks.run (SourceGraph.Incidence.endpoint S p) (4*count S p) le_rfl).ranks

theorem rank_value (S : Source.SparseSystem) (p : ℕ) (i : Fin (4*count S p)) :
    (rank S p i).val=(rankValues S p).get i := by
  rw [rank,IncidenceRanks.ranks_get_val,rankValues,IncidenceRanks.rank_eq _ _ _ _ i.isLt]

def source (S : Source.SparseSystem) (p : ℕ) (i : Fin (4*count S p)) : Fin (size S p) :=
  Fin.cast (size_eq S p) (PortIndices.sourcePort (half S p) (vertex_room S p)
    (SourceGraph.Incidence.endpoint S p) (rank S p) i)
def target (S : Source.SparseSystem) (p : ℕ) (i : Fin (4*count S p)) : Fin (size S p) :=
  Fin.cast (size_eq S p) (PortIndices.targetPort (half S p) (incidence_room S p) i)

theorem source_injective (S : Source.SparseSystem) (p : ℕ) : Function.Injective (source S p) := by
  intro a b hab
  apply PortIndices.sourcePort_injective (half S p) (vertex_room S p)
    (SourceGraph.Incidence.endpoint S p) (rank S p)
    (IncidenceRanks.endpoint_rank_injective _ (SourceGraph.Incidence.endpoint_degree S p))
  exact Fin.ext (congrArg (fun x : Fin (size S p) => x.val) hab)

theorem target_injective (S : Source.SparseSystem) (p : ℕ) : Function.Injective (target S p) := by
  intro a b hab
  apply PortIndices.targetPort_injective (half S p) (incidence_room S p)
  exact Fin.ext (congrArg (fun x : Fin (size S p) => x.val) hab)

def plan (S : Source.SparseSystem) (p : ℕ) (clock : List Bool)
    (room : dimension S p<2^width S p) : Scatter.Plan (4*count S p) (size S p) where
  routing := Startup.gridLayout (vertices S p) (base S p)
  inputLayout := GraphIncidence.layout (width S p) (dimension S p) (count S p)
  clock := clock
  half := half S p
  half_pos := by unfold half portHalfSide; positivity
  endpoint := IncidenceEncoding.endpointValues (SourceGraph.Incidence.endpoint S p)
  rank := rankValues S p
  source := source S p
  target := target S p
  source_eq := by
    intro i
    simpa only [source,Fin.val_cast,rank_value,IncidenceEncoding.endpointValues_get] using
      PortIndices.sourcePort_value (half S p) (vertex_room S p)
        (SourceGraph.Incidence.endpoint S p) (rank S p) i
  target_eq := by intro i; rfl
  width_pos := by dsimp [GraphIncidence.layout]; omega
  endpoint_fits := by
    intro i
    rw [IncidenceEncoding.endpointValues_get]
    have hi := (SourceGraph.Incidence.endpoint S p i).isLt
    have hc : count S p≤3*dimension S p := Logical.sourceSquareEntries_length_le S p
    dsimp [GraphIncidence.layout]
    rw [pow_add]
    norm_num
    omega
  rank_fits := by
    intro i
    have h := IncidenceEncoding.run_ranks_lt_three (SourceGraph.Incidence.endpoint S p)
      (SourceGraph.Incidence.endpoint_degree S p) (4*count S p) le_rfl i
    change (rankValues S p).get i<4
    exact h.trans (by decide)
  endpoint_forward := Or.inl (by
    dsimp [GraphIncidence.layout,Startup.gridLayout,Startup.layout,base,vertices]
    omega)
  endpoint_backward := Or.inl (by
    dsimp [GraphIncidence.layout,Startup.gridLayout,Startup.layout,base,vertices]
    omega)
  rank_forward := Or.inl (by
    dsimp [GraphIncidence.layout,Startup.gridLayout,Startup.layout,base,vertices]
    omega)
  rank_backward := Or.inl (by
    dsimp [GraphIncidence.layout,Startup.gridLayout,Startup.layout,base,vertices]
    omega)

#print axioms plan
#print axioms source_injective
#print axioms target_injective

end Maxwell.Cost.RoutingPorts.Complete.SourcePlan
