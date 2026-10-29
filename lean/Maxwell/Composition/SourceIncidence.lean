import Maxwell.Composition.SourceSubdivisionDegree
import Maxwell.Composition.SourceDefectLayout
import Maxwell.Composition.DecoratedLattice

/-! Canonical oriented edges of the actual routed source matrix. The
orientation is the increasing coordinate sum on each unit lattice edge. -/
noncomputable section
namespace Maxwell.Composition.SourceIncidence
open Maxwell.Spectral.Lattice Maxwell.Logical.Routing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable (S : Source.SparseSystem) (precision : ℕ)
local instance : DecidableEq (SourceRouting.Vertex S precision) := Classical.decEq _

abbrev V := SourceRouting.Vertex S precision
abbrev position := SourceDefectLayout.position S precision

theorem position_eq (v : V S precision) : position S precision v =
    ![(SourceRouting.embedding S precision v).1 + 4,
      (SourceRouting.embedding S precision v).2.1 + 4,
      (SourceRouting.embedding S precision v).2.2 + 16] := by
  have h := Subdivision.embedding_box (SourceRouting.data S precision) v
  unfold SortSchedule.InHorizontalBox at h
  ext k
  fin_cases k <;>
    dsimp [position, SourceDefectLayout.position, SourceDefectLayout.indices,
      SourceRouting.boxIndex, Subdivision.boxIndex, Target.latticeCell,
      SourceRouting.embedding] <;> omega

theorem matrix_adjacent (u v : V S precision) (hne : u ≠ v)
    (h : SourceSubdivision.matrix S precision u v ≠ 0) :
    DecoratedLattice.Adjacent (position S precision u) (position S precision v) := by
  rw [DecoratedLattice.adjacent_iff, position_eq, position_eq]
  have hl := SourceSubdivision.matrix_local S precision u v hne h
  simpa [UnitAdjacent] using hl

def height (x : Site) : ℤ := x 0 + x 1 + x 2

theorem height_add_unit (x : Site) (k : Direction) :
    height (x + unitSite k) = height x + 1 := by
  fin_cases k <;> simp [height, unitSite] <;> ring

theorem adjacent_height_ne (x y : Site) (h : DecoratedLattice.Adjacent x y) :
    height x ≠ height y := by
  rcases h with ⟨k, rfl | rfl⟩ <;> rw [height_add_unit] <;> omega

def E := {uv : V S precision × V S precision //
  SourceSubdivision.matrix S precision uv.1 uv.2 = 1 ∧
    height (position S precision uv.1) < height (position S precision uv.2)}

instance : Fintype (E S precision) := inferInstanceAs (Fintype {_uv : V S precision × V S precision // _})
instance : DecidableEq (E S precision) := Classical.decEq _

def graph : SignedIncidence (V S precision) (E S precision) where
  tail e := e.val.1
  head e := e.val.2
  distinct e := by intro h; have he := e.property.2; rw [h] at he; omega
  sign _ := 1
  abs_sign _ := abs_one

theorem edge_oriented (e : E S precision) : ∃ k : Direction,
    position S precision e.val.2 = position S precision e.val.1 + unitSite k := by
  have ha := matrix_adjacent S precision e.val.1 e.val.2 ((graph S precision).distinct e)
    (by rw [e.property.1]; norm_num)
  rcases ha with ⟨k, h | h⟩
  · exact ⟨k, h⟩
  · have hh := e.property.2
    rw [h, height_add_unit] at hh
    omega

def axis (e : E S precision) : Direction := (edge_oriented S precision e).choose

theorem axis_spec (e : E S precision) :
    position S precision e.val.2 = position S precision e.val.1 + unitSite (axis S precision e) :=
  (edge_oriented S precision e).choose_spec

theorem oriented_sum (u v : V S precision) :
    (∑ e : E S precision, if u = e.val.1 ∧ v = e.val.2 then (1 : ℝ) else 0) =
      if SourceSubdivision.matrix S precision u v = 1 ∧
        height (position S precision u) < height (position S precision v) then 1 else 0 := by
  by_cases hp : SourceSubdivision.matrix S precision u v = 1 ∧
      height (position S precision u) < height (position S precision v)
  · let e : E S precision := ⟨(u, v), hp⟩
    rw [ite_eq_left hp, Finset.sum_eq_single e]
    · simp [e]
    · intro f _ hfe
      apply ite_eq_right
      rintro ⟨hu, hv⟩
      apply hfe
      apply Subtype.ext
      exact Prod.ext hu.symm hv.symm
    · simp
  · rw [ite_eq_right hp]
    apply Finset.sum_eq_zero
    intro e _
    apply ite_eq_right
    rintro ⟨hu, hv⟩
    exact hp (hu ▸ hv ▸ e.property)

theorem adjacency_eq (u v : V S precision) :
    (graph S precision).adjacency u v =
      if u = v then 0 else SourceSubdivision.matrix S precision u v := by
  change (∑ e : E S precision,
    ((if u = e.val.1 ∧ v = e.val.2 then (1 : ℝ) else 0) +
      (if u = e.val.2 ∧ v = e.val.1 then (1 : ℝ) else 0))) = _
  rw [Finset.sum_add_distrib]
  have hr : (∑ e : E S precision, if u = e.val.2 ∧ v = e.val.1 then (1 : ℝ) else 0) =
      ∑ e : E S precision, if v = e.val.1 ∧ u = e.val.2 then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    simp only [and_comm]
  rw [hr, oriented_sum, oriented_sum, ← SourceSubdivision.matrix_symmetric S precision u v]
  by_cases huv : u = v
  · subst v
    simp
  · rw [ite_eq_right huv]
    rcases SourceSubdivision.offdiagonal_zero_or_one S precision u v huv with hz | ho
    · simp [hz]
    · have hn := adjacent_height_ne _ _ (matrix_adjacent S precision u v huv (by rw [ho]; norm_num))
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · simp [ho, hlt, not_lt_of_ge (le_of_lt hlt)]
      · simp [ho, hgt, not_lt_of_ge (le_of_lt hgt)]

theorem logicalMatrix_eq :
    (graph S precision).logicalMatrix (fun u => SourceSubdivision.matrix S precision u u) =
      SourceSubdivision.matrix S precision := by
  ext u v
  rw [SignedIncidence.logicalMatrix, Matrix.add_apply, adjacency_eq]
  by_cases h : u = v
  · subst v; simp
  · simp [h]

theorem degree_eq (u : V S precision) :
    (graph S precision).degree u =
      ∑ v : V S precision, if v = u then 0 else |SourceSubdivision.matrix S precision u v| := by
  have hsum : (graph S precision).degree u = ∑ v, (graph S precision).adjacency u v := by
    simp only [SignedIncidence.degree, SignedIncidence.adjacency]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_add_distrib]
    change (if u = e.val.1 ∨ u = e.val.2 then (1 : ℝ) else 0) =
      (∑ v : V S precision, if u = e.val.1 ∧ v = e.val.2 then 1 else 0) +
      ∑ v : V S precision, if u = e.val.2 ∧ v = e.val.1 then 1 else 0
    have hn := (graph S precision).distinct e
    change e.val.1 ≠ e.val.2 at hn
    by_cases hu : u = e.val.1 <;> by_cases hv : u = e.val.2 <;> simp_all
  rw [hsum]
  apply Finset.sum_congr rfl
  intro v _
  rw [adjacency_eq]
  by_cases hv : v = u
  · subst v; simp
  · rcases SourceSubdivision.offdiagonal_zero_or_one S precision u v (Ne.symm hv) with h | h <;>
      simp [hv, Ne.symm hv, h]

theorem degree_le_three (u : V S precision) : (graph S precision).degree u ≤ 3 := by
  rw [degree_eq]
  exact SourceSubdivision.offdiag_row_abs_sum_le_three S precision u

end Maxwell.Composition.SourceIncidence
