import Maxwell.Continuum.SourceRoutingLevelWidths
import Maxwell.Continuum.SourceRoutingTreeCoordinates

/-! Every incoming permutation of a level lies in the completed parent
level. The runtime controller preserves the level geometry as it advances. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Level
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem coordinates_values (v : ℕ→ℕ) (heap rootCount rootWidth d n w : ℕ)
    (hs : Coordinates.Stored v heap rootCount rootWidth d n w 0) (i : ℕ) :
    Coordinates.Stored (values v i) heap rootCount rootWidth d n w i := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact (values_other v i 806 (by decide)).trans hs.heap
  · exact (values_other v i 809 (by decide)).trans hs.stride
  · exact (values_other v i 811 (by decide)).trans hs.count
  · exact (values_other v i 812 (by decide)).trans hs.width
  · exact (values_other v i 814 (by decide)).trans hs.first
  · rw [values_index,hs.index];omega
  · exact (values_other v i 819 (by decide)).trans hs.two

theorem quotient_values (v : ℕ→ℕ) (i j : ℕ)
    (hj : j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts) : values v i j=v j := by
  apply values_other
  have hh : Disjoint Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts writes := by decide
  exact Finset.disjoint_left.mp hh hj

theorem block_before (heap rootCount rootWidth a b : ℕ) (h : a<b) :
    block heap rootCount rootWidth a+stride rootCount rootWidth ≤ block heap rootCount rootWidth b := by
  have hh:=Nat.mul_le_mul_right (stride rootCount rootWidth) (show a+1 ≤ b by omega)
  dsimp only [block]
  nlinarith only [hh]

theorem inputs_before_first (v : ℕ→ℕ) (heap rootCount rootWidth d n w : ℕ)
    (i : Fin (2^d)) (b : Bool)
    (hs : Coordinates.Stored v heap rootCount rootWidth (d+1) n w (Targets.child d i b).val)
    (hn : 2*n ≤ rootCount) (hw : w+1 ≤ rootWidth) :
    Descriptor.output v 803+n*w ≤ block heap rootCount rootWidth (2^(d+1)-1) ∧
      Descriptor.output v 804+n*w ≤ block heap rootCount rootWidth (2^(d+1)-1) := by
  rw [Coordinates.forward_eq v heap rootCount rootWidth d n w i b hs,
    Coordinates.backward_eq v heap rootCount rootWidth d n w i b hs]
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  have hsize : n*w ≤ (2*n)*(w+1) := Nat.mul_le_mul (by omega) (by omega)
  have hf := (slab_fits heap rootCount rootWidth (levelNode d i) (2*n) (w+1)
    (6+2*b.toNat) hn hw (by omega)).2
  have hr := (slab_fits heap rootCount rootWidth (levelNode d i) (2*n) (w+1)
    (7+2*b.toNat) hn hw (by omega)).2
  have hp:=block_before heap rootCount rootWidth (levelNode d i) (2^(d+1)-1) (level_range d i).2
  constructor <;> omega

#print axioms coordinates_values
#print axioms inputs_before_first
end Maxwell.Cost.RoutingPorts.Complete.Tree.Level
