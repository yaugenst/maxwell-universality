import Maxwell.Cost.RealSparseOrder.MergeInvariant
import Maxwell.Cost.RealSimulation.IndexWidth

namespace Maxwell.Cost.RealSparseOrder
open RealSimulation.IndexWidth

/-- A buffer endpoint bounds both its current cursor and all later cursors. -/
def Within (B : ℕ) (b : Buffer) (n : ℕ) : Prop :=
  b.coordinates+2*n≤B ∧b.coefficients+n≤B

theorem Within.subset {B : ℕ} {b : Buffer} {m i n : ℕ}
    (h : Within B b m) (hi : i+n≤m) : Within B (b.shift i) n := by
  simp only [Within,Buffer.shift] at *
  constructor <;> omega

theorem compare_index_bound {B : ℕ} {s : RAMState} {a b out : Buffer} {xs ys : List SparseEntry}
    (h : Merge.Invariant s a b out xs ys) (hs : IndexBound B s)
    (ha : Within B a xs.length) (hb : Within B b ys.length)
    (hx : 0<xs.length) (hy : 0<ys.length) : IndexBound B (Compare.loaded s) := by
  have hla : s.indices 6+1≤B := by rw [h.config.leftRow]; unfold Within at ha; omega
  have hlb : s.indices 8+1≤B := by rw [h.config.rightRow]; unfold Within at hb; omega
  unfold Compare.loaded
  exact (((((hs.setIndex 13 _ (hs _)).setIndex 12 _ hla).setIndex 14 _ (hs _)).setIndex 15 _
    (hs _)).setIndex 12 _ hlb).setIndex 16 _ (hs _)

theorem emit_index_bound (left : Bool) {B : ℕ} {s : RAMState} {a b out : Buffer}
    {xs ys : List SparseEntry} (h : Merge.Invariant s a b out xs ys)
    (hs : IndexBound B s) (ha : Within B a xs.length) (hb : Within B b ys.length)
    (ho : Within B out (xs.length+ys.length))
    (hne : if left then 0<xs.length else 0<ys.length) : IndexBound B (Emit.advanced left s) := by
  have hsrc : s.indices (Emit.rowRegister left)+2≤B ∧
      s.indices (Emit.valueRegister left)+1≤B := by
    cases left <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hne
    · simp only [Emit.rowRegister,Emit.valueRegister,Bool.false_eq_true,ite_false]
      rw [h.config.rightRow,h.config.rightValue]
      unfold Within at hb
      constructor <;> omega
    · simp only [Emit.rowRegister,Emit.valueRegister,ite_true]
      rw [h.config.leftRow,h.config.leftValue]
      unfold Within at ha
      constructor <;> omega
  have htotal : 0<xs.length+ys.length := by cases left <;> simp at hne <;> omega
  have hout : s.indices 10+2≤B ∧s.indices 11+1≤B := by
    rw [h.config.outRow,h.config.outValue]
    unfold Within at ho
    constructor <;> omega
  have hrow : (Emit.head s (s.indices (Emit.rowRegister left))
      (s.indices (Emit.valueRegister left))).row≤B := hs _
  have hcol : (Emit.head s (s.indices (Emit.rowRegister left))
      (s.indices (Emit.valueRegister left))).column≤B := hs _
  have hm : IndexBound B (Emit.middle left s) := by
    unfold Emit.middle
    exact (((((hs.setIndex 13 _ hrow).setIndex 12 _ (by omega)).setIndex 14 _ hcol).setIndex
      (s.indices 10) _ hrow).setIndex 12 _ (by omega)).setIndex (s.indices 10+1) _ hcol
  unfold Emit.advanced
  exact (((((hm.setIndex (Emit.rowRegister left) _ hsrc.1).setIndex (Emit.valueRegister left) _ hsrc.2).setIndex (Emit.countRegister left) _ ((Nat.sub_le _ _).trans (hs _))).setIndex 5 _
      ((Nat.sub_le _ _).trans (hs _))).setIndex 10 _ hout.1).setIndex 11 _ hout.2

end Maxwell.Cost.RealSparseOrder
