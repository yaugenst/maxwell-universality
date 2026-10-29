import Maxwell.Logical.Routing.Coloring
import Maxwell.Logical.Routing.PlacementArrays

/-! One executable network backend from a prescribed permutation to stored
cubic-lattice output. Correctness is linked to the all-input geometric proof. -/

namespace Maxwell.Logical.Routing.Executable

open Maxwell.Logical.Routing.Schedule
open Maxwell.Logical.Routing.SortSchedule
open Maxwell.Logical.Routing.SortArrays
open Maxwell.Logical.Routing.PlacementArrays

/-- Every partial placement in the stored schedule equals the proved one. -/
theorem full_placement {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (level : ℕ) (hl : level ≤ 6 * q) :
    placement (fullSchedule colors) level = placement (permutationSchedule colors) level :=
  placement_congr _ _ level (fun t ht => fullSchedule_eq colors t (by omega))

theorem full_point {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target)
    (level : Fin (6 * q)) (token : Port q) (step : ℕ) :
    emittedPoint (fullSchedule colors) (history (fullSchedule colors) (6 * q)) level token step =
      (routes (permutationSchedule colors) (6 * q)).point level token step := by
  rw [emittedPoint_eq]
  simp only [routes]
  rw [fullSchedule_eq colors _ level.isLt, full_placement colors _ (by omega)]

theorem full_length {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target)
    (level : Fin (6 * q)) (token : Port q) :
    emittedLength (fullSchedule colors) (history (fullSchedule colors) (6 * q)) level token =
      (routes (permutationSchedule colors) (6 * q)).length level token := by
  rw [emittedLength_eq]
  simp only [routes]
  rw [fullSchedule_eq colors _ level.isLt, full_placement colors _ (by omega)]

/-- Every cached emitted point is one of the already certified network vertices. -/
theorem full_point_box {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target)
    (level : Fin (6 * q)) (token : Port q) (step : ℕ)
    (hs : step < emittedLength (fullSchedule colors) (history (fullSchedule colors) (6 * q)) level token) :
    let p := emittedPoint (fullSchedule colors) (history (fullSchedule colors) (6 * q)) level token step
    InHorizontalBox q p ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ 96 * q := by
  rw [full_length] at hs
  simpa only [full_point, Assembly.trajectoryPoint] using
    permutationSchedule_box colors token (Sum.inl ⟨level, ⟨step, hs⟩⟩)

/-- Compile a power-of-two square permutation, constructing its coloring,
stored phase inverses, sorting arrays, placement arrays, and output points. -/
def network (depth : ℕ) (target : Equiv.Perm (Port (2 ^ depth))) : List Point :=
  let colors := Coloring.rowColoring depth target
  let schedule := fullSchedule colors
  emitInteriors schedule (6 * 2 ^ depth)

/-- The output size is bounded by the actual at-most-forty-edge local paths. -/
theorem network_length (depth : ℕ) (target : Equiv.Perm (Port (2 ^ depth))) :
    (network depth target).length ≤ 240 * (2 ^ depth) ^ 3 := by
  have hh := emitInteriors_length_le (fullSchedule (Coloring.rowColoring depth target)) (6 * 2 ^ depth)
  calc
    (network depth target).length ≤ 40 * (6 * 2 ^ depth) * (2 ^ depth * 2 ^ depth) := hh
    _ = 240 * (2 ^ depth) ^ 3 := by ring

/-- The complete constructed routing reaches the supplied target permutation. -/
theorem network_endpoint (depth : ℕ) (target : Equiv.Perm (Port (2 ^ depth))) :
    placement (fullSchedule (Coloring.rowColoring depth target)) (6 * 2 ^ depth) = target :=
  fullSchedule_routes_target _

end Maxwell.Logical.Routing.Executable
