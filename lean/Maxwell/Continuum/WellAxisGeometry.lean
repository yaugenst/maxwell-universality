import Maxwell.Composition.SourceEdgeGeometry
import Maxwell.Continuum.SourceGeometryPacking

/-! The mediator axis is obtained by two coordinate comparisons on the
chronological samples. The orientation of a path does not affect it. -/
namespace Maxwell.Composition.SourceEdgeList
open Maxwell.Logical.Routing Maxwell.Spectral.Lattice
set_option maxHeartbeats 1800000

theorem direction_swap (p q : Point) : direction (q,p)=direction (p,q) := by
  simp only [direction,ne_comm]

noncomputable section
variable (S : Source.SparseSystem) (p : ℕ)

theorem direction_pair (s : SourceSteps.Step S p) :
    direction (SourceSegmentList.pair S p s)=
      SourceIncidence.axis S p (SourceEdgeEnumeration.toEdge S p s) := by
  have h := direction_eq S p (SourceEdgeEnumeration.toEdge S p s)
  rcases SourceEdgeEnumeration.toEdge_endpoints S p s with he | he
  · simpa only [coordinate,SourceSegmentList.pair,he.1,he.2] using h
  · simpa only [coordinate,SourceSegmentList.pair,he.1,he.2,direction_swap] using h

end
end Maxwell.Composition.SourceEdgeList

namespace Maxwell.Continuum.WellAxis
open Maxwell.Logical.Routing Maxwell.Spectral.Lattice
open Maxwell.Composition.SourceDecorationEnumeration

def select {α : Type*} [DecidableEq α] (x₀ y₀ x₁ y₁ : α) : Direction :=
  if x₀≠y₀ then 0 else if x₁≠y₁ then 1 else 2

theorem shifted_select (p q : Point) :
    select (shiftedPoint p 0) (shiftedPoint q 0) (shiftedPoint p 1) (shiftedPoint q 1)=
      Maxwell.Composition.SourceEdgeList.direction (p,q) := by
  simp [select,shiftedPoint,Maxwell.Composition.SourceEdgeList.direction]

theorem natural_select (x y : Site) (hx : ∀k,0≤x k) (hy : ∀k,0≤y k) :
    select (x 0).toNat (y 0).toNat (x 1).toNat (y 1).toNat=select (x 0) (y 0) (x 1) (y 1) := by
  have eqv (k : Direction) : (x k).toNat=(y k).toNat ↔ x k=y k := by
    constructor
    · intro he
      have := congrArg (fun n:ℕ=>(n:ℤ)) he
      simpa only [Int.toNat_of_nonneg (hx k),Int.toNat_of_nonneg (hy k)] using this
    · exact congrArg Int.toNat
  simp only [select,ne_eq,eqv]

#print axioms Maxwell.Composition.SourceEdgeList.direction_pair
end Maxwell.Continuum.WellAxis
