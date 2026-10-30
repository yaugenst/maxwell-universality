import Maxwell.Continuum.SourceRoutingLevelCoordinates

/-! The level execution specification is instantiated entirely from
stored tree coordinates, logical target permutations, and initial word widths. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Level
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def ofCoordinates (rows columns d heap rootCount rootWidth L : ℕ) (v : ℕ→ℕ)
    (target : Fin (2^(d+1))→Targets.Target rows (columns+1))
    (hL : 1 ≤ L)
    (hn : 2*(2*2^(columns+rows)) ≤ rootCount) (hw : columns+rows+3 ≤ rootWidth)
    (hs : Coordinates.Stored v heap rootCount rootWidth (d+1)
      (2*2^(columns+rows)) (columns+rows+2) 0)
    (hz : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0)
    (hv : ∀j∈Division.ids,(v j).bits.length ≤ L) (hp : (2^(d+1)).bits.length ≤ L) :
    Plan (columns+rows) where
  initial:=v
  nodes:=2^(d+1)
  heap:=heap
  rootCount:=rootCount
  rootWidth:=rootWidth
  first:=2^(d+1)-1
  B:=uniformWidth L
  B_lower:=by dsimp only [uniformWidth];omega
  count_fits:=by omega
  width_fits:=by omega
  data:=fun i => ColorData.splitData rows columns (target i)
  colors:=fun i => ColorData.splitData_colors rows columns (target i)
  count:=fun i _ => (coordinates_values v heap rootCount rootWidth (d+1) _ _ hs i).count
  width:=fun i _ => (coordinates_values v heap rootCount rootWidth (d+1) _ _ hs i).width
  two:=fun i _ => (coordinates_values v heap rootCount rootWidth (d+1) _ _ hs i).two
  zero:=by intro i _ j hj;rw [quotient_values v i j hj];exact hz j hj
  words:=by
    intro i hi
    exact values_width v i L hL hv ((Maxwell.Continuum.RationalWords.bits_mono (Nat.le_of_lt hi)).trans hp)
  address:=by
    intro i hi
    let idx : Fin (2^(d+1)):=⟨i,hi⟩
    have hc : Coordinates.Stored (values v i) heap rootCount rootWidth (d+1)
        (2*2^(columns+rows)) (columns+rows+2) (Targets.child d (Targets.parent d idx) (Targets.bit idx)).val := by
      rw [Targets.child_parent]
      exact coordinates_values v heap rootCount rootWidth (d+1) _ _ hs i
    have hh:=Coordinates.heap_eq (values v i) heap rootCount rootWidth d _ _
      (Targets.parent d idx) (Targets.bit idx) hc
    simpa only [Targets.child_parent,levelNode] using hh
  separated:=by
    intro i hi
    let idx : Fin (2^(d+1)):=⟨i,hi⟩
    have hc : Coordinates.Stored (values v i) heap rootCount rootWidth (d+1)
        (2*2^(columns+rows)) (columns+rows+2) (Targets.child d (Targets.parent d idx) (Targets.bit idx)).val := by
      rw [Targets.child_parent]
      exact coordinates_values v heap rootCount rootWidth (d+1) _ _ hs i
    exact Coordinates.input_separated (values v i) heap rootCount rootWidth d _ _
      (Targets.parent d idx) (Targets.bit idx) hc
  forward_before:=by
    intro i hi
    let idx : Fin (2^(d+1)):=⟨i,hi⟩
    have hc : Coordinates.Stored (values v i) heap rootCount rootWidth (d+1)
        (2*2^(columns+rows)) (columns+rows+2) (Targets.child d (Targets.parent d idx) (Targets.bit idx)).val := by
      rw [Targets.child_parent]
      exact coordinates_values v heap rootCount rootWidth (d+1) _ _ hs i
    exact (inputs_before_first (values v i) heap rootCount rootWidth d _ _
      (Targets.parent d idx) (Targets.bit idx) hc hn hw).1
  backward_before:=by
    intro i hi
    let idx : Fin (2^(d+1)):=⟨i,hi⟩
    have hc : Coordinates.Stored (values v i) heap rootCount rootWidth (d+1)
        (2*2^(columns+rows)) (columns+rows+2) (Targets.child d (Targets.parent d idx) (Targets.bit idx)).val := by
      rw [Targets.child_parent]
      exact coordinates_values v heap rootCount rootWidth (d+1) _ _ hs i
    exact (inputs_before_first (values v i) heap rootCount rootWidth d _ _
      (Targets.parent d idx) (Targets.bit idx) hc hn hw).2

#print axioms ofCoordinates
end Maxwell.Cost.RoutingPorts.Complete.Tree.Level
