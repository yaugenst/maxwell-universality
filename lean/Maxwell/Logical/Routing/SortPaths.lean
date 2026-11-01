import Maxwell.Logical.Routing.SortArrays

/-! Paths through a stored sorting history. These recurrences and their
forward/reverse identities depend only on the logical routing network. -/
namespace Maxwell.Logical.Routing.SortPaths
open Schedule

def port {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) : ℕ→Port q
  | 0 => start
  | k+1 => RowLayer.destination (SortArrays.arraySelection (k+1) (SortArrays.run initial k))
      (port initial start k)

def length {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (k : ℕ) : ℕ :=
  RowLayer.pathLength (SortArrays.arraySelection (k+1) (SortArrays.run initial k))
    (port initial start k)

def count {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) : ℕ→ℕ
  | 0 => 0
  | k+1 => count initial start k+3*length initial start k

theorem length_bound {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (k : ℕ) :
    length initial start k ≤ 40 :=
  (rowLayer (SortArrays.arraySelection (k+1) (SortArrays.run initial k))).length_le _

theorem count_bound {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (k : ℕ) :
    count initial start k ≤ 120*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := length_bound initial start k
    change count initial start k+3*length initial start k ≤ 120*(k+1)
    omega

/-- Reversing one layer reads the same stored comparison decisions. -/
theorem port_reverse_step {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (k : ℕ) :
    RowLayer.destination (SortArrays.arraySelection (k+1) (SortArrays.run initial k))
      (port initial start (k+1)) = port initial start k :=
  RowLayer.destination_involutive _ _

theorem layer_destination {q : ℕ} (initial : SortArrays.Keys q) (k : ℕ) (p : Port q) :
    RowLayer.destination (SortArrays.arraySelection (k+1) (SortArrays.run initial k)) p =
      (SortSchedule.rowSchedule q (SortArrays.word initial) k).next p := by
  have active : (SortArrays.arraySelection (k+1) (SortArrays.run initial k)).active =
      (SortSchedule.selection q ((k+1)%2)
        (SortSchedule.keyState q (SortArrays.word initial) k)).active := by
    funext col row
    simp [SortArrays.arraySelection,SortSchedule.selection,
      BinaryDepth.mem_layerCenters,SortArrays.run_word,and_assoc]
  have movement : RowLayer.movement (SortArrays.arraySelection (k+1) (SortArrays.run initial k)) p =
      RowLayer.movement (SortSchedule.selection q ((k+1)%2)
        (SortSchedule.keyState q (SortArrays.word initial) k)) p := by
    simp only [RowLayer.movement,active]
  change RowLayer.destination (SortArrays.arraySelection (k+1) (SortArrays.run initial k)) p =
    RowLayer.destination (SortSchedule.selection q ((k+1)%2)
      (SortSchedule.keyState q (SortArrays.word initial) k)) p
  apply Prod.ext
  · apply Fin.ext
    simp only [RowLayer.destination,RowLayer.destinationColumn,movement]
  · rfl

theorem port_placement {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (k : ℕ) :
    port initial start k = placement (SortSchedule.rowSchedule q (SortArrays.word initial)) k start := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [port,ih,layer_destination]
    rfl

theorem port_target {q : ℕ} (target : Equiv.Perm (Port q))
    (row : ∀p,(target p).2=p.2) (start : Port q) :
    port (SortArrays.targetArray target) start (2*q) = target start := by
  rw [port_placement,SortArrays.targetArray_word,SortSchedule.rowSchedule_routes_target target row]

#print axioms port_reverse_step
#print axioms port_target
end Maxwell.Logical.Routing.SortPaths
