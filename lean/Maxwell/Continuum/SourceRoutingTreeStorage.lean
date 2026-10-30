import Maxwell.Continuum.SourceRoutingIndexedMemory
import Maxwell.Continuum.SourceRoutingTreeTargets
import Maxwell.Cost.ChildPermutation.Correctness

/-! Logical recursive targets and the machine's stored forward and inverse
arrays have the same bit-level contents, including across size casts. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Storage
open Maxwell.Logical.Routing Coloring Coloring.NumericSplit
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def Permutation (rows columns : ℕ) (target : Targets.Target rows columns)
    (memory : ℕ→Bool) (base width : ℕ) : Prop :=
  IndexedMemory.Represents (ColorData.index rows columns)
    (fun p => (ColorData.index rows columns (target p)).val) memory base width

theorem cast_columns (rows : ℕ) {a b : ℕ} (h : a=b) (target : Targets.Target rows a)
    (memory : ℕ→Bool) (base width : ℕ) :
    Permutation rows a target memory base width ↔
      Permutation rows b (Targets.castTarget rows h target) memory base width := by
  subst b
  rfl

theorem numeric (rows columns : ℕ) (target : Targets.Target rows columns)
    (memory : ℕ→Bool) (base width : ℕ) :
    Permutation rows columns target memory base width ↔
      BitArray.Represents memory base width (DoublingPass.words width
        (Vector.ofFn (numericPerm (ColorData.index rows columns) target))) :=
  IndexedMemory.numeric _ _ _ _ _

theorem index_value_succ (rows columns : ℕ) (p : Columns (columns+1)×Fin (2^rows)) :
    (ColorData.index rows (columns+1) p).val=(halfIndex (ColorData.index rows columns) p).val := by
  rw [ColorData.index_succ]
  rfl

theorem split_target (rows columns : ℕ) (target : Targets.Target rows (columns+1))
    (memory : ℕ→Bool) (base width : ℕ) :
    Permutation rows (columns+1) target memory base width ↔
      BitArray.Represents memory base width (DoublingPass.words width
        (Vector.ofFn (ColorData.splitData rows columns target).target)) := by
  change _ ↔ BitArray.Represents memory base width (DoublingPass.words width
    (Vector.ofFn (numericPerm (halfIndex (ColorData.index rows columns)) target)))
  rw [←IndexedMemory.numeric (halfIndex (ColorData.index rows columns)) target memory base width]
  exact (IndexedMemory.congr_index (ColorData.index rows (columns+1))
    (halfIndex (ColorData.index rows columns)) (index_value_succ rows columns)
    (fun p => (ColorData.index rows (columns+1) (target p)).val) memory base width).trans
    (IndexedMemory.congr_value (halfIndex (ColorData.index rows columns))
      (fun p => (ColorData.index rows (columns+1) (target p)).val)
      (fun p => (halfIndex (ColorData.index rows columns) (target p)).val)
      (fun p => index_value_succ rows columns (target p)) memory base width)

theorem inverse_numeric {α : Type*} {n : ℕ} (idx : α≃Fin n) (target : Equiv.Perm α) :
    numericPerm idx target.symm=(numericPerm idx target).symm := by
  ext i
  rfl

theorem split_inverse (rows columns : ℕ) (target : Targets.Target rows (columns+1))
    (memory : ℕ→Bool) (base width : ℕ) :
    Permutation rows (columns+1) target.symm memory base width ↔
      BitArray.Represents memory base width (DoublingPass.words width
        (Vector.ofFn (ColorData.splitData rows columns target).target.symm)) := by
  have hh := split_target rows columns target.symm memory base width
  change _ ↔ BitArray.Represents memory base width (DoublingPass.words width
    (Vector.ofFn (numericPerm (halfIndex (ColorData.index rows columns)) target).symm))
  rw [←inverse_numeric (halfIndex (ColorData.index rows columns)) target]
  exact hh

theorem final_words {k : ℕ} (width : ℕ) (data : ChildPermutation.Data k) (j : Fin 4) :
    ChildPermutation.finalOutputs width data j=
      DoublingPass.words width (Vector.ofFn (data.finalPerm j)) := by
  apply Vector.ext
  intro i hi
  simp [ChildPermutation.finalOutputs,DoublingPass.words,IncidenceEncoding.words]

theorem child_forward (rows columns : ℕ) (target : Targets.Target rows (columns+1))
    (layout : ChildPermutation.Layout) (memory : ℕ→Bool)
    (h : ChildPermutation.Represents layout memory (ColorData.splitData rows columns target)
      (ChildPermutation.finalOutputs layout.childWidth (ColorData.splitData rows columns target))) (b : Bool) :
    Permutation rows columns (ColorData.childTarget rows columns target b) memory
      (layout.outputBase ⟨2*b.toNat,by cases b <;> decide⟩) layout.childWidth := by
  apply (numeric _ _ _ _ _ _).mpr
  cases b
  · have hh:=h.outputs 0
    rw [final_words,ChildPermutation.Data.finalPerm_zero,ColorData.splitData_left] at hh
    exact hh
  · have hh:=h.outputs 2
    rw [final_words,ChildPermutation.Data.finalPerm_two,ColorData.splitData_right] at hh
    exact hh

theorem child_backward (rows columns : ℕ) (target : Targets.Target rows (columns+1))
    (layout : ChildPermutation.Layout) (memory : ℕ→Bool)
    (h : ChildPermutation.Represents layout memory (ColorData.splitData rows columns target)
      (ChildPermutation.finalOutputs layout.childWidth (ColorData.splitData rows columns target))) (b : Bool) :
    Permutation rows columns (ColorData.childTarget rows columns target b).symm memory
      (layout.outputBase ⟨2*b.toNat+1,by cases b <;> decide⟩) layout.childWidth := by
  apply (numeric _ _ _ _ _ _).mpr
  cases b
  · have hh:=h.outputs 1
    rw [final_words,ChildPermutation.Data.finalPerm_one,ColorData.splitData_left,←inverse_numeric] at hh
    exact hh
  · have hh:=h.outputs 3
    rw [final_words,ChildPermutation.Data.finalPerm_three,ColorData.splitData_right,←inverse_numeric] at hh
    exact hh

#print axioms split_target
#print axioms child_forward
#print axioms child_backward
end Maxwell.Cost.RoutingPorts.Complete.Tree.Storage
