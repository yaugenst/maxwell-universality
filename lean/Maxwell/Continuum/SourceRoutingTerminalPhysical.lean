import Maxwell.Continuum.SourceRoutingTerminalEmit

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured Maxwell.Logical.Routing

 def bottomCode (part backwards : Bool) : Code := terminalCode true (bottomChoice part) backwards
 def topCode : Code := terminalCode false (.shape .top) false
 def endpointCode : Code := terminalCode false (.shape .endpoint) false

theorem bottom_shape {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (p : GeometrySort.Plan (2*half)) (round : ℕ) (incidence : Gluing.Incidence E) (cursor : ℕ) :
    (bottomChoice incidence.2).evaluate (terminalValues p round (Gluing.token data incidence) cursor true)=
      .bottom (data.part (data.endpoint incidence.1 incidence.2)) (data.arm incidence.1 incidence.2) := by
  rw [data.endpoint_part]
  exact bottom_selects p round _ _ cursor incidence.2

theorem bottom_shape_length {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (p : GeometrySort.Plan (2*half)) (round : ℕ) (incidence : Gluing.Incidence E) (cursor : ℕ) :
    ((bottomChoice incidence.2).evaluate (terminalValues p round (Gluing.token data incidence) cursor true)).length=
      (EdgeEmission.bottomPrefix data incidence).length := by
  rw [bottom_shape]
  simp only [Shape.length,EdgeEmission.bottomPrefix,List.length_map,List.length_range]

theorem bottom_bits {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (p : GeometrySort.Plan (2*half)) (round : ℕ) (incidence : Gluing.Incidence E) (cursor width : ℕ) (backwards : Bool) :
    let v := terminalValues p round (Gluing.token data incidence) cursor true
    entryBits width v (((bottomChoice incidence.2).evaluate v).entries false backwards)=
      pointsBits width (if backwards then (EdgeEmission.bottomPrefix data incidence).reverse
        else EdgeEmission.bottomPrefix data incidence) := by
  dsimp only
  rw [bottom_shape]
  exact bottomBits_meaning data incidence width _ (bottom_origin p round _ _ cursor) backwards

theorem top_bits {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (p : GeometrySort.Plan (2*half)) (round : ℕ) (edge : E) (cursor width : ℕ) :
    entryBits width (terminalValues p round (Gluing.pairPort (data.pair edge) false) cursor false)
      (Shape.top.entries false false)=pointsBits width (EdgeEmission.topPrefix data edge) :=
  topBits_meaning data edge width _ (top_origin p round (data.pair edge) cursor)

theorem endpoint_bits {q : ℕ} (p : GeometrySort.Plan q) (round : ℕ) (port : Port q) (cursor width : ℕ) :
    entryBits width (terminalValues p round port cursor false) (Shape.endpoint.entries false false)=
      pointsBits width [Schedule.gridPort port (96*q)] := by
  rw [endpointBits_meaning,endpoint_origin]

#print axioms bottom_bits
#print axioms top_bits
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
