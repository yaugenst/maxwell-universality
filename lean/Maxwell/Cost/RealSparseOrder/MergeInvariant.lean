import Maxwell.Cost.RealSparseOrder.MergeState

namespace Maxwell.Cost.RealSparseOrder.Merge
open RealSimulation.Control

/-- Source records are immutable during a merge; the destination interval
is disjoint from each source. The two sources may be adjacent or overlap. -/
structure Invariant (s : RAMState) (a b out : Buffer) (xs ys : List SparseEntry) : Prop where
  config : Config s a xs.length b ys.length out
  safeLeft : a.Safe
  safeRight : b.Safe
  safeOut : out.Safe
  left : Records a s xs
  right : Records b s ys
  sepLeft : Separated a xs.length out (xs.length+ys.length)
  sepRight : Separated b ys.length out (xs.length+ys.length)

@[simp] theorem invariant_ofState (s : RAMState) (a b out : Buffer) (xs ys : List SparseEntry) :
    Invariant (Store.ofState s).val a b out xs ys ↔Invariant s a b out xs ys := by
  constructor <;> intro h
  · exact ⟨(config_ofState _ _ _ _ _ _).mp h.config,h.safeLeft,h.safeRight,h.safeOut,(records_ofState _ _ _).mp h.left,
      (records_ofState _ _ _).mp h.right,h.sepLeft,h.sepRight⟩
  · exact ⟨(config_ofState _ _ _ _ _ _).mpr h.config,h.safeLeft,h.safeRight,h.safeOut,(records_ofState _ _ _).mpr h.left,
      (records_ofState _ _ _).mpr h.right,h.sepLeft,h.sepRight⟩

theorem Invariant.compare {s : RAMState} {a b out : Buffer} {xs ys : List SparseEntry}
    (h : Invariant s a b out xs ys) : Invariant (Compare.loaded s) a b out xs ys := by
  refine ⟨h.config.compare,h.safeLeft,h.safeRight,h.safeOut,?_,?_,h.sepLeft,h.sepRight⟩
  · exact h.left.frame h.safeLeft (by simp [Separated]) (compare_frame s ⟨0,0⟩)
  · exact h.right.frame h.safeRight (by simp [Separated]) (compare_frame s ⟨0,0⟩)

theorem Invariant.emit_ready {s : Store} {a b out : Buffer} {xs ys : List SparseEntry}
    (h : Invariant s.val a b out xs ys) (left : Bool) : Emit.Ready left s.val := by
  refine ⟨s.property,h.config.one,h.config.two,?_,?_,?_,?_⟩
  · cases left <;> simp only [Emit.rowRegister,Bool.false_eq_true,ite_false,ite_true]
    · rw [h.config.rightRow]; exact h.safeRight.2
    · rw [h.config.leftRow]; exact h.safeLeft.2
  · cases left <;> simp only [Emit.valueRegister,Bool.false_eq_true,ite_false,ite_true]
    · rw [h.config.rightValue]; exact h.safeRight.1
    · rw [h.config.leftValue]; exact h.safeLeft.1
  · rw [h.config.outRow]; exact h.safeOut.2
  · rw [h.config.outValue]; exact h.safeOut.1

theorem Invariant.compare_ready {s : Store} {a b out : Buffer} {xs ys : List SparseEntry}
    (h : Invariant s.val a b out xs ys) : Compare.Ready s.val := by
  refine ⟨s.property,h.config.one,?_,?_⟩
  · rw [h.config.leftRow]; exact h.safeLeft.2
  · rw [h.config.rightRow]; exact h.safeRight.2

theorem Invariant.left_head {s : RAMState} {a b out : Buffer} {e : SparseEntry}
    {xs ys : List SparseEntry} (h : Invariant s a b out (e::xs) ys) :
    Emit.head s (s.indices (Emit.rowRegister true)) (s.indices (Emit.valueRegister true))=e := by
  change SparseEntry.mk (s.indices (s.indices 6)) (s.indices (s.indices 6+1))
    (s.words (s.indices 7))=e
  rw [h.config.leftRow,h.config.leftValue,h.left.1,h.left.2.1,h.left.2.2.1]

theorem Invariant.right_head {s : RAMState} {a b out : Buffer} {e : SparseEntry}
    {xs ys : List SparseEntry} (h : Invariant s a b out xs (e::ys)) :
    Emit.head s (s.indices (Emit.rowRegister false)) (s.indices (Emit.valueRegister false))=e := by
  change SparseEntry.mk (s.indices (s.indices 8)) (s.indices (s.indices 8+1))
    (s.words (s.indices 9))=e
  rw [h.config.rightRow,h.config.rightValue,h.right.1,h.right.2.1,h.right.2.2.1]

theorem Invariant.emit_left {s : RAMState} {a b out : Buffer} {e : SparseEntry}
    {xs ys : List SparseEntry} (h : Invariant s a b out (e::xs) ys) :
    Invariant (Emit.advanced true s) (a.shift 1) b (out.shift 1) xs ys := by
  have frame := emit_frame true h.config
  have sl : Separated (a.shift 1) xs.length out 1 := by
    simpa using h.sepLeft.subset (i:=1) (r:=xs.length) (j:=0) (q:=1) (by simp; omega) (by simp; omega)
  have sr : Separated b ys.length out 1 := by
    simpa using h.sepRight.subset (i:=0) (r:=ys.length) (j:=0) (q:=1) (by simp) (by simp; omega)
  refine ⟨h.config.emit_left h.safeOut,h.safeLeft.shift 1,h.safeRight,h.safeOut.shift 1,
    h.left.2.2.2.frame (h.safeLeft.shift 1) sl frame,
    h.right.frame h.safeRight sr frame,?_,?_⟩
  · exact h.sepLeft.subset (i:=1) (r:=xs.length) (j:=1) (q:=xs.length+ys.length)
      (by simp; omega) (by simp; omega)
  · simpa using h.sepRight.subset (i:=0) (r:=ys.length) (j:=1) (q:=xs.length+ys.length)
      (by simp) (by simp; omega)

theorem Invariant.emit_right {s : RAMState} {a b out : Buffer} {e : SparseEntry}
    {xs ys : List SparseEntry} (h : Invariant s a b out xs (e::ys)) :
    Invariant (Emit.advanced false s) a (b.shift 1) (out.shift 1) xs ys := by
  have frame := emit_frame false h.config
  have sl : Separated a xs.length out 1 := by
    simpa using h.sepLeft.subset (i:=0) (r:=xs.length) (j:=0) (q:=1) (by simp) (by simp; omega)
  have sr : Separated (b.shift 1) ys.length out 1 := by
    simpa using h.sepRight.subset (i:=1) (r:=ys.length) (j:=0) (q:=1) (by simp; omega) (by simp; omega)
  refine ⟨h.config.emit_right h.safeOut,h.safeLeft,h.safeRight.shift 1,h.safeOut.shift 1,
    h.left.frame h.safeLeft sl frame,
    h.right.2.2.2.frame (h.safeRight.shift 1) sr frame,?_,?_⟩
  · simpa using h.sepLeft.subset (i:=0) (r:=xs.length) (j:=1) (q:=xs.length+ys.length)
      (by simp) (by simp; omega)
  · exact h.sepRight.subset (i:=1) (r:=ys.length) (j:=1) (q:=xs.length+ys.length)
      (by simp; omega) (by simp; omega)

end Maxwell.Cost.RealSparseOrder.Merge
