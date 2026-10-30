import Maxwell.Continuum.SourceRoutingAssemblyTraversalWidth

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyTraversal
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def values (v : ℕ→ℕ) (total : ℕ) : ℕ→ℕ→ℕ
  | 0 => v
  | r+1 => AssemblyLevel.nextValues (values v total r) (2^(total-(r+1)))

theorem coordinates (v : ℕ→ℕ) (heap rootCount rootWidth rows total : ℕ)
    (hs : AssemblyCoordinates.Stored v heap rootCount rootWidth (total-1) rows 0)
    (r : ℕ) (hr : r<total) :
    AssemblyCoordinates.Stored (values v total r) heap rootCount rootWidth
      (total-(r+1)) (r+rows) 0 := by
  induction r with
  | zero => simpa only [values,Nat.zero_add] using hs
  | succ r ih =>
      have prior:=ih (by omega)
      have current:=AssemblyLevel.coordinates (values v total r) heap rootCount rootWidth _ _ prior
        (2^(total-(r+1)))
      have depth : total-(r+1)=(total-(r+2))+1 := by omega
      have current2 : AssemblyCoordinates.Stored
          (AssemblyLevel.values (values v total r) (2^(total-(r+1)))) heap rootCount rootWidth
          (total-(r+2)+1) (r+rows) (2^(total-(r+1))) := by
        rw [←depth]
        exact current
      have next:=AssemblyAdvance.coordinates _ heap rootCount rootWidth (total-(r+2)) (r+rows) _ current2
      have width : r+rows+1=r+1+rows := by omega
      rw [width] at next
      simpa only [values,AssemblyLevel.nextValues,show r+1+1=r+2 by omega] using next

theorem population (v : ℕ→ℕ) (total : ℕ) (hp : v 813=2^(total-1)) (htwo : v 819=2)
    (r : ℕ) (hr : r<total) : values v total r 813=2^(total-(r+1)) ∧ values v total r 819=2 := by
  induction r with
  | zero => exact ⟨hp,htwo⟩
  | succ r ih =>
      have prior:=ih (by omega)
      have depth : total-(r+1)=total-(r+2)+1 := by omega
      constructor
      · change AssemblyAdvance.output (AssemblyLevel.values (values v total r) _) 813=2^(total-(r+1+1))
        rw [AssemblyAdvance.output_population,AssemblyLevel.values_other _ _ 813 (by decide),
          AssemblyLevel.values_other _ _ 819 (by decide),prior.1,prior.2,depth,pow_succ]
        rw [show r+1+1=r+2 by omega]
        omega
      · exact (AssemblyAdvance.output_other _ 819 (by decide)).trans
          ((AssemblyLevel.values_other _ _ 819 (by decide)).trans prior.2)

theorem quotient_zero (v : ℕ→ℕ) (total : ℕ)
    (hz : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0) (r : ℕ) :
    ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,values v total r i=0 := by
  induction r with
  | zero => exact hz
  | succ r ih =>
      apply AssemblyAdvance.quotient_zero
      intro i hi
      have disjoint : Disjoint Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts AssemblyLevel.writes := by decide
      rw [AssemblyLevel.values_other _ _ i (Finset.disjoint_left.mp disjoint hi)]
      exact ih i hi

def width (heap rows total : ℕ) : ℕ :=
  AssemblyLevel.uniformWidth (baseWidth heap (2^(total+rows)) (total+rows+1) total)

theorem words (v : ℕ→ℕ) (heap rows total : ℕ)
    (hs : AssemblyCoordinates.Stored v heap (2^(total+rows)) (total+rows+1) (total-1) rows 0)
    (hp : v 813=2^(total-1))
    (hv : ∀i∈Division.ids,(v i).bits.length ≤ width heap rows total)
    (r : ℕ) (hr : r ≤ total) :
    ∀i∈Division.ids,(values v total r i).bits.length ≤ width heap rows total := by
  induction r with
  | zero => exact hv
  | succ r ih =>
      have coords:=coordinates v heap (2^(total+rows)) (total+rows+1) rows total hs r (by omega)
      have pop:=population v total hp hs.two r (by omega)
      exact completed_width _ heap (2^(total+rows)) (total+rows+1) total _ _ coords pop.1
        (by omega) (Nat.pow_le_pow_right (by decide) (by omega)) (by omega) (ih (by omega))

#print axioms coordinates
#print axioms population
#print axioms words
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyTraversal
