import Maxwell.Continuum.SourceRoutingNetwork
import Maxwell.Continuum.SourceRoutingTerminalPhysical
import Maxwell.Continuum.SourceRoutingTerminalPair

/-! Fixed whole-edge program and its chronological point accounting. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryPathPhase Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def edgeCode : Code := .seq (bottomCode false false)
  (.seq GeometryPathPhase.threePhaseCode (.seq topCode (.seq (NatAssign.code pairSwitch)
    (.seq endpointCode (.seq GeometryPathReverse.threePhaseCode (bottomCode true true))))))

def terminalCost {q : ℕ} (p : GeometrySort.Plan q) (round width base n : ℕ) : ℕ :=
  2^142*(terminalBound p round width base n+3)^2

def edgeCost {q : ℕ} (p : Plan q)
    (sep₁ : p.history.following.slab (2*q+1) ≤ p.base)
    (sep₂ : p.history.following.following.slab (2*q+1) ≤ p.base) (n : ℕ) : ℕ :=
  2*terminalCost (p.history.layer 0) 1 p.width p.base n+networkForwardCost p sep₁ sep₂ n+
    2*terminalCost (p.history.following.following.layer (2*q)) (2*q+1) p.width p.base n+
    2^16*((p.history.following.following.layer (2*q)).bound (2*q+1)+2)^2+networkReverseCost p sep₁ sep₂ n

theorem write_points_append (memory : ℕ→Bool) (base width cursor : ℕ) (xs ys : List Point) :
    MemoryWord.writeBits (MemoryWord.writeBits memory (base+cursor*width) (pointsBits width xs))
      (base+(cursor+3*xs.length)*width) (pointsBits width ys)=
      MemoryWord.writeBits memory (base+cursor*width) (pointsBits width (xs++ys)) := by
  have address : base+(cursor+3*xs.length)*width=base+cursor*width+(pointsBits width xs).length := by
    rw [pointsBits_length]
    ring
  rw [address,writeBits_append,pointsBits_append]

theorem network_words_bound {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (incidence : Gluing.Incidence E) :
    3*(EdgeEmission.networkPrefix (EdgeEmission.prepare data) (Gluing.token data incidence)).length ≤ 720*(2*half) := by
  have h := SortPaths.threePhase_count data.colors (Gluing.token data incidence)
  rw [SortPaths.threePhasePoints_network] at h
  have a := SortPaths.count_bound (PhaseKeys.first data.colors) (Gluing.token data incidence) (2*(2*half))
  have b := SortPaths.count_bound (PhaseKeys.middle data.colors)
    (nextStart (PhaseKeys.first data.colors) (Gluing.token data incidence)) (2*(2*half))
  have c := SortPaths.count_bound (PhaseKeys.last data.colors)
    (nextStart (PhaseKeys.middle data.colors) (nextStart (PhaseKeys.first data.colors) (Gluing.token data incidence))) (2*(2*half))
  omega

theorem bottom_words_bound {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (incidence : Gluing.Incidence E) : 3*(EdgeEmission.bottomPrefix data incidence).length ≤ 192 := by
  have h := (Shape.bottom (data.part (data.endpoint incidence.1 incidence.2)) (data.arm incidence.1 incidence.2)).length_bound
  simp only [Shape.length,EdgeEmission.bottomPrefix,List.length_map,List.length_range] at h ⊢
  omega

theorem top_prefix_length {V E : Type*} {half : ℕ} (data : Gluing.Data V E half) (edge : E) :
    (EdgeEmission.topPrefix data edge).length=48 := by simp [EdgeEmission.topPrefix]

theorem edge_parts {V E : Type*} {half : ℕ} (data : Gluing.Data V E half) (edge : E) :
    EdgeEmission.edge data (EdgeEmission.prepare data) edge=
      EdgeEmission.bottomPrefix data (edge,false)++
      EdgeEmission.networkPrefix (EdgeEmission.prepare data) (Gluing.token data (edge,false))++
      EdgeEmission.topPrefix data edge++[Schedule.gridPort (Gluing.pairPort (data.pair edge) true) (96*(2*half))]++
      (EdgeEmission.networkPrefix (EdgeEmission.prepare data) (Gluing.token data (edge,true))).reverse++
      (EdgeEmission.bottomPrefix data (edge,true)).reverse := by
  simp only [EdgeEmission.edge,EdgeEmission.legPoints,List.reverse_append,List.reverse_singleton,List.append_assoc]

#print axioms network_words_bound
#print axioms edge_parts
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
