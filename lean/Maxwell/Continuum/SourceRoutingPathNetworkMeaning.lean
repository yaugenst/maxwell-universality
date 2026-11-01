import Maxwell.Continuum.SourceRoutingPathPhaseMeaning
import Maxwell.Logical.Routing.SortPathsGeometryCount

/-! The emitted row-column-row words are the canonical lattice walk samples.
The equalities remove all machine cursor and scratch-memory choices. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Maxwell.Logical.Routing


theorem pointsBits_length (width : ℕ) (points : List Point) :
    (pointsBits width points).length=3*points.length*width := by
  induction points with
  | nil => simp [pointsBits]
  | cons p ps ih =>
    rw [show p::ps=[p]++ps by rfl,pointsBits_append,List.length_append,ih]
    simp only [pointsBits,Maxwell.Composition.SourceDecorationEnumeration.pointWords,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,IncidenceEncoding.word_length,
      List.length_cons,List.length_nil]
    ring

theorem threePhaseBits_meaning {q : ℕ} (p : GeometryPathPhase.Plan q)
    (separated₁ : p.history.following.slab (2*q+1) ≤ p.base)
    (separated₂ : p.history.following.following.slab (2*q+1) ≤ p.base)
    {target : Equiv.Perm (Port q)} (colors : RowColoring target) (start : Port q) (cursor : ℕ) :
    GeometryPathPhase.threePhaseBits p separated₁ separated₂
      (PhaseKeys.first colors) (PhaseKeys.middle colors) (PhaseKeys.last colors) start cursor=
      pointsBits p.width (SortPaths.threePhasePoints colors start) := by
  simp only [GeometryPathPhase.threePhaseBits,phaseBits_meaning,GeometryPathPhase.Plan.following,
    SortPaths.threePhasePoints,pointsBits_append]

theorem reverseThreePhaseBits_meaning {q : ℕ} (p : GeometryPathPhase.Plan q)
    (separated₁ : p.history.following.slab (2*q+1) ≤ p.base)
    (separated₂ : p.history.following.following.slab (2*q+1) ≤ p.base)
    {target : Equiv.Perm (Port q)} (colors : RowColoring target) (start : Port q) (cursor : ℕ) :
    GeometryPathReverse.threePhaseBits p separated₁ separated₂
      (PhaseKeys.first colors) (PhaseKeys.middle colors) (PhaseKeys.last colors) start cursor=
      pointsBits p.width ((SortPaths.threePhasePoints colors start).reverse) := by
  simp only [GeometryPathReverse.threePhaseBits,reversePhaseBits_end,GeometryPathPhase.Plan.following,
    SortPaths.threePhasePoints,List.reverse_append,pointsBits_append,List.append_assoc]

theorem threePhaseBits_network {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (p : GeometryPathPhase.Plan (2*half))
    (separated₁ : p.history.following.slab (2*(2*half)+1) ≤ p.base)
    (separated₂ : p.history.following.following.slab (2*(2*half)+1) ≤ p.base)
    (incidence : Gluing.Incidence E) (cursor : ℕ) :
    GeometryPathPhase.threePhaseBits p separated₁ separated₂
      (PhaseKeys.first data.colors) (PhaseKeys.middle data.colors) (PhaseKeys.last data.colors)
      (Gluing.token data incidence) cursor=
      pointsBits p.width (EdgeEmission.networkPrefix (EdgeEmission.prepare data) (Gluing.token data incidence)) := by
  rw [threePhaseBits_meaning,SortPaths.threePhasePoints_network]

theorem reverseThreePhaseBits_network {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (p : GeometryPathPhase.Plan (2*half))
    (separated₁ : p.history.following.slab (2*(2*half)+1) ≤ p.base)
    (separated₂ : p.history.following.following.slab (2*(2*half)+1) ≤ p.base)
    (incidence : Gluing.Incidence E) (cursor : ℕ) :
    GeometryPathReverse.threePhaseBits p separated₁ separated₂
      (PhaseKeys.first data.colors) (PhaseKeys.middle data.colors) (PhaseKeys.last data.colors)
      (Gluing.token data incidence) cursor=
      pointsBits p.width ((EdgeEmission.networkPrefix (EdgeEmission.prepare data) (Gluing.token data incidence)).reverse) := by
  rw [reverseThreePhaseBits_meaning,SortPaths.threePhasePoints_network]

#print axioms threePhaseBits_network
#print axioms reverseThreePhaseBits_network
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
