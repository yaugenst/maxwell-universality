import Maxwell.Logical.Routing.Assembly
import Maxwell.Logical.Routing.RowLayer

/-! Explicit composition of computed row and column swap layers into
simple, disjoint three-dimensional token trajectories. -/

namespace Maxwell.Logical.Routing.Schedule

open Maxwell.Logical.Routing
open Maxwell.Logical.Routing.Assembly

/-- Standard array port at an integral height. -/
def gridPort {q : ℕ} (p : Port q) (height : ℤ) : Point :=
  (16 * (p.1.val : ℤ), 16 * (p.2.val : ℤ), height)

theorem gridPort_injective (q : ℕ) (height : ℤ) :
    Function.Injective (fun p : Port q => gridPort p height) := by
  intro a b he
  simp only [gridPort, Prod.mk.injEq] at he
  apply Prod.ext <;> apply Fin.ext <;> omega

/-- One concrete unit-height slab, with its computed port permutation. -/
structure CubicLayer (q : ℕ) where
  next : Equiv.Perm (Port q)
  length : Port q → ℕ
  point : Port q → ℕ → Point
  length_le : ∀ p, length p ≤ 40
  first : ∀ p, point p 0 = gridPort p 0
  last : ∀ p, point p (length p) = gridPort (next p) 16
  step : ∀ p t, t < length p → UnitAdjacent (point p t) (point p (t + 1))
  slab : ∀ p t, t ≤ length p → 0 ≤ (point p t).2.2 ∧ (point p t).2.2 ≤ 16
  faces : ∀ p t, t ≤ length p →
    ((point p t).2.2 = 0 ↔ t = 0) ∧ ((point p t).2.2 = 16 ↔ t = length p)
  injective : ∀ a b i j, i ≤ length a → j ≤ length b → point a i = point b j → a = b ∧ i = j

/-- Instantiate a cubic layer with the actual swap/vertical paths. -/
def rowLayer {q parity : ℕ} (selected : RowLayer.Selection q parity) : CubicLayer q where
  next := RowLayer.destinationPermutation selected
  length := RowLayer.pathLength selected
  point := RowLayer.pathPoint selected
  length_le p := by cases hm : RowLayer.movement selected p <;> simp [RowLayer.pathLength, hm]
  first := RowLayer.pathPoint_first selected
  last := RowLayer.pathPoint_last selected
  step := RowLayer.pathPoint_steps selected
  slab := RowLayer.pathPoint_slab selected
  faces := RowLayer.pathPoint_faces selected
  injective := RowLayer.pathPoint_injective selected

/-- Exchange array rows and columns. -/
def swapPorts (q : ℕ) : Equiv.Perm (Port q) := Equiv.prodComm _ _

@[simp] theorem transpose_gridPort {q : ℕ} (p : Port q) (z : ℤ) :
    transposeXY (gridPort p z) = gridPort (swapPorts q p) z := rfl

/-- Transpose a computed row layer into a computed column layer. -/
def columnLayer {q parity : ℕ} (selected : RowLayer.Selection q parity) : CubicLayer q where
  next := ((swapPorts q).trans (rowLayer selected).next).trans (swapPorts q)
  length p := (rowLayer selected).length (swapPorts q p)
  point p t := transposeXY ((rowLayer selected).point (swapPorts q p) t)
  length_le p := (rowLayer selected).length_le _
  first p := by rw [(rowLayer selected).first, transpose_gridPort]; rfl
  last p := by rw [(rowLayer selected).last, transpose_gridPort]; rfl
  step p t ht := (transposeXY_unit_adjacent _ _).mpr ((rowLayer selected).step _ t ht)
  slab p t ht := (rowLayer selected).slab _ t ht
  faces p t ht := (rowLayer selected).faces _ t ht
  injective a b i j hi hj he := by
    have hh := (rowLayer selected).injective _ _ i j hi hj (transposeXY_injective he)
    exact ⟨(swapPorts q).injective hh.1, hh.2⟩

/-- Execute computed port permutations from one slab to the next. -/
def placement {q : ℕ} (schedule : ℕ → CubicLayer q) : ℕ → Equiv.Perm (Port q)
  | 0 => Equiv.refl _
  | t + 1 => (placement schedule t).trans (schedule t).next

/-- The actual layer paths translated to their successive vertical slabs. -/
def routes {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ) :
    LayeredRoutes (Port q) layers where
  length l token := (schedule l.val).length (placement schedule l.val token)
  point l token step := translate (0, 0, 16 * (l.val : ℤ))
    ((schedule l.val).point (placement schedule l.val token) step)
  port level token := gridPort (placement schedule level.val token) (16 * level.val)
  port_height level token := rfl
  port_injective level := (gridPort_injective q (16 * level.val)).comp (placement schedule level.val).injective
  first level token := by
    rw [(schedule level.val).first]
    simp only [translate, gridPort, zero_add, add_zero, Fin.val_castSucc]
  last level token := by
    rw [(schedule level.val).last]
    simp only [translate, gridPort, zero_add, Fin.val_succ, placement, Equiv.trans_apply]
    congr 2
  step level token i hi := (translate_unit_adjacent _ _ _).mpr ((schedule level.val).step _ i hi)
  slab level token i hi := by
    have hh := (schedule level.val).slab (placement schedule level.val token) i hi
    simp only [translate]
    push_cast
    omega
  lower_index level token i hi hz := by
    have hf := (schedule level.val).faces (placement schedule level.val token) i hi
    simp only [translate] at hz
    exact hf.1.mp (by omega)
  upper_index level token i hi hz := by
    have hf := (schedule level.val).faces (placement schedule level.val token) i hi
    simp only [translate] at hz
    push_cast at hz
    exact hf.2.mp (by omega)
  layer_injective level a b i j hi hj he := by
    have hh := (schedule level.val).injective _ _ i j hi hj (translate_injective _ he)
    exact ⟨(placement schedule level.val).injective hh.1, hh.2⟩

/-- Arbitrary computed row/column layer schedules produce an actual
injective embedding of all token trajectories in the cubic lattice. -/
theorem schedule_trajectory_injective {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ) :
    Function.Injective (fun entry : Σ token, TrajectoryIndex (routes schedule layers) token =>
      trajectoryPoint (routes schedule layers) entry.1 entry.2) :=
  trajectory_embedding_injective (routes schedule layers)

/-- The emitted trajectory length is the sum of its actual slab lengths. -/
def trajectoryLength {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ) (token : Port q) : ℕ :=
  ∑ level : Fin layers, (routes schedule layers).length level token

theorem trajectoryLength_le {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ) (token : Port q) :
    trajectoryLength schedule layers token ≤ 40 * layers := by
  calc
    trajectoryLength schedule layers token ≤ ∑ _level : Fin layers, 40 :=
      Finset.sum_le_sum (fun level _ => (schedule level.val).length_le _)
    _ = 40 * layers := by simp [Nat.mul_comm]

end Maxwell.Logical.Routing.Schedule
