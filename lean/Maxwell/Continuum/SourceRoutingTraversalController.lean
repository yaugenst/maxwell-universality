import Maxwell.Continuum.SourceRoutingLevelCompleted
import Maxwell.Continuum.SourceRoutingTraversalWidth

/-! Closed invariants for all iterations of the fixed outer routing
loop.  Stored coordinates and one uniform bit bound are derived, not
supplied separately at each level. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Traversal
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def values (v : ℕ→ℕ) : ℕ→ℕ→ℕ
  | 0 => v
  | d+1 => Level.nextValues (values v d) (2^(d+1))

theorem coordinates (v : ℕ→ℕ) (heap rootCount rootWidth rows total : ℕ)
    (hs : Coordinates.Stored v heap rootCount rootWidth 1
      (2^(total-1+rows)) (total-1+rows+1) 0)
    (d : ℕ) (hd : d+1 ≤ total) :
    Coordinates.Stored (values v d) heap rootCount rootWidth (d+1)
      (2^(total-(d+1)+rows)) (total-(d+1)+rows+1) 0 := by
  induction d with
  | zero => exact hs
  | succ d ih =>
      have prior:=ih (by omega)
      have current:=Level.coordinates_values (values v d) heap rootCount rootWidth (d+1) _ _ prior (2^(d+1))
      have next:=Level.Advance.coordinates _ heap rootCount rootWidth (d+1) _ _ _ (by omega) current
      have exponent : total-(d+1)+rows=(total-(d+2)+rows)+1 := by omega
      have count : (2 : ℕ)^(total-(d+1)+rows)/2=2^(total-(d+2)+rows) := by
        rw [exponent,pow_succ]
        omega
      have width : total-(d+1)+rows+1-1=total-(d+2)+rows+1 := by omega
      rw [count,width] at next
      exact next

theorem population (v : ℕ→ℕ) (hp : v 813=2) (htwo : v 819=2) (d : ℕ) :
    values v d 813=2^(d+1) ∧ values v d 819=2 := by
  induction d with
  | zero => exact ⟨hp,htwo⟩
  | succ d ih =>
      constructor
      · change Level.Advance.output (Level.values (values v d) (2^(d+1))) 813=2^(d+1+1)
        rw [Level.Advance.output_nodes,Level.values_other _ _ 819 (by decide),
          Level.values_other _ _ 813 (by decide),ih.1,ih.2]
        exact (pow_succ' 2 (d+1)).symm
      · exact (Level.Advance.output_other _ 819 (by decide)).trans
          ((Level.values_other _ _ 819 (by decide)).trans ih.2)

theorem quotient_zero (v : ℕ→ℕ)
    (hz : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0) (d : ℕ) :
    ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,values v d i=0 := by
  induction d with
  | zero => exact hz
  | succ d ih =>
      apply Level.Advance.quotient_zero
      intro i hi
      rw [Level.quotient_values _ _ i hi]
      exact ih i hi

theorem words (v : ℕ→ℕ) (heap rows total : ℕ)
    (hs : Coordinates.Stored v heap (2^(total+rows)) (total+rows+1) 1
      (2^(total-1+rows)) (total-1+rows+1) 0)
    (hp : v 813=2)
    (hv : ∀i∈Division.ids,(v i).bits.length ≤
      Level.uniformWidth (ControllerWidth.baseWidth heap (2^(total+rows)) (total+rows+1) total))
    (d : ℕ) (hd : d+1 ≤ total) :
    ∀i∈Division.ids,(values v d i).bits.length ≤
      Level.uniformWidth (ControllerWidth.baseWidth heap (2^(total+rows)) (total+rows+1) total) := by
  induction d with
  | zero => exact hv
  | succ d ih =>
      have coord:=coordinates v heap (2^(total+rows)) (total+rows+1) rows total hs d (by omega)
      have pop:=population v hp hs.two d
      exact ControllerWidth.completed_width _ heap (2^(total+rows)) (total+rows+1) total (d+1) _ _
        coord pop.1 (by omega) (Nat.pow_le_pow_right (by decide) (by omega)) (by omega) (ih (by omega))

theorem visit_coordinates (v : ℕ→ℕ) (heap rootCount rootWidth rows total : ℕ)
    (hs : Coordinates.Stored v heap rootCount rootWidth 1
      (2^(total-1+rows)) (total-1+rows+1) 0)
    (d : ℕ) (hd : d+1<total) :
    Coordinates.Stored (values v d) heap rootCount rootWidth (d+1)
      (2*2^(total-(d+2)+rows)) (total-(d+2)+rows+2) 0 := by
  have hh:=coordinates v heap rootCount rootWidth rows total hs d (by omega)
  have he : total-(d+1)+rows=(total-(d+2)+rows)+1 := by omega
  rw [he,pow_succ'] at hh
  exact hh

#print axioms coordinates
#print axioms words
#print axioms visit_coordinates
end Maxwell.Cost.RoutingPorts.Complete.Tree.Traversal
