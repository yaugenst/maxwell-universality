import Maxwell.Cost.RealSparseOrder.Compare
import Maxwell.Cost.RealSparseOrder.Memory

namespace Maxwell.Cost.RealSparseOrder.Merge
open RealSimulation.Control

structure Config (s : RAMState) (a : Buffer) (m : ℕ) (b : Buffer) (n : ℕ) (out : Buffer) : Prop where
  zero : s.indices 0=0
  one : s.indices 1=1
  two : s.indices 2=2
  leftCount : s.indices 3=m
  rightCount : s.indices 4=n
  total : s.indices 5=m+n
  leftRow : s.indices 6=a.coordinates
  leftValue : s.indices 7=a.coefficients
  rightRow : s.indices 8=b.coordinates
  rightValue : s.indices 9=b.coefficients
  outRow : s.indices 10=out.coordinates
  outValue : s.indices 11=out.coefficients

@[simp] theorem config_ofState (s : RAMState) (a b out : Buffer) (m n : ℕ) :
    Config (Store.ofState s).val a m b n out ↔Config s a m b n out := by
  constructor <;> intro h <;> exact ⟨h.zero,h.one,h.two,h.leftCount,h.rightCount,h.total,
    h.leftRow,h.leftValue,h.rightRow,h.rightValue,h.outRow,h.outValue⟩

@[simp] theorem records_ofState (s : RAMState) (b : Buffer) (es : List SparseEntry) :
    Records b (Store.ofState s).val es ↔Records b s es := by
  induction es generalizing b with
  | nil => rfl
  | cons e es ih =>
    simp only [Records]
    rw [ih]
    rfl

theorem Config.compare {s : RAMState} {a b out : Buffer} {m n : ℕ}
    (h : Config s a m b n out) : Config (Compare.loaded s) a m b n out := by
  constructor
  · exact (Compare.indices_frame s 0 (Or.inl (by omega))).trans h.zero
  · exact (Compare.indices_frame s 1 (Or.inl (by omega))).trans h.one
  · exact (Compare.indices_frame s 2 (Or.inl (by omega))).trans h.two
  · exact (Compare.indices_frame s 3 (Or.inl (by omega))).trans h.leftCount
  · exact (Compare.indices_frame s 4 (Or.inl (by omega))).trans h.rightCount
  · exact (Compare.indices_frame s 5 (Or.inl (by omega))).trans h.total
  · exact (Compare.indices_frame s 6 (Or.inl (by omega))).trans h.leftRow
  · exact (Compare.indices_frame s 7 (Or.inl (by omega))).trans h.leftValue
  · exact (Compare.indices_frame s 8 (Or.inl (by omega))).trans h.rightRow
  · exact (Compare.indices_frame s 9 (Or.inl (by omega))).trans h.rightValue
  · exact (Compare.indices_frame s 10 (Or.inl (by omega))).trans h.outRow
  · exact (Compare.indices_frame s 11 (Or.inl (by omega))).trans h.outValue

theorem compare_frame (s : RAMState) (out : Buffer) :
    MemoryFrame out 0 s (Compare.loaded s) := by
  constructor
  · intro j hj _
    exact Compare.indices_frame s j (Or.inr hj)
  · intro j _ _
    rfl

theorem emit_frame (left : Bool) {s : RAMState} {a b out : Buffer} {m n : ℕ}
    (h : Config s a m b n out) : MemoryFrame out 1 s (Emit.advanced left s) := by
  constructor
  · intro j hj ho
    apply Emit.indices_frame left s j hj
    · rw [h.outRow]; omega
    · rw [h.outRow]; omega
  · intro j hj ho
    apply Emit.words_frame left s j (by omega)
    rw [h.outValue]; omega

set_option maxHeartbeats 800000 in
theorem Config.emit_left {s : RAMState} {a b out : Buffer} {m n : ℕ}
    (h : Config s a (m+1) b n out) (ho : out.Safe) :
    Config (Emit.advanced true s) (a.shift 1) m b n (out.shift 1) := by
  have hd : ∀j:ℕ,j<17→j≠out.coordinates := by unfold Buffer.Safe at ho; omega
  have hd1 : ∀j:ℕ,j<17→j≠out.coordinates+1 := by unfold Buffer.Safe at ho; omega
  have hz : out.coordinates≠0 := by unfold Buffer.Safe at ho; omega
  constructor <;> simp [Emit.advanced,Emit.middle,RAMState.setIndex,RAMState.setWord,
    Emit.rowRegister,Emit.valueRegister,Emit.countRegister,Buffer.shift,
    hd,hd1,hz,h.zero,h.one,h.two,h.leftCount,h.rightCount,h.total,
    h.leftRow,h.leftValue,h.rightRow,h.rightValue,h.outRow,h.outValue,Nat.add_sub_assoc,Nat.add_assoc]

set_option maxHeartbeats 800000 in
theorem Config.emit_right {s : RAMState} {a b out : Buffer} {m n : ℕ}
    (h : Config s a m b (n+1) out) (ho : out.Safe) :
    Config (Emit.advanced false s) a m (b.shift 1) n (out.shift 1) := by
  have hd : ∀j:ℕ,j<17→j≠out.coordinates := by unfold Buffer.Safe at ho; omega
  have hd1 : ∀j:ℕ,j<17→j≠out.coordinates+1 := by unfold Buffer.Safe at ho; omega
  have hz : out.coordinates≠0 := by unfold Buffer.Safe at ho; omega
  constructor <;> simp [Emit.advanced,Emit.middle,RAMState.setIndex,RAMState.setWord,
    Emit.rowRegister,Emit.valueRegister,Emit.countRegister,Buffer.shift,
    hd,hd1,hz,h.zero,h.one,h.two,h.leftCount,h.rightCount,h.total,
    h.leftRow,h.leftValue,h.rightRow,h.rightValue,h.outRow,h.outValue,Nat.add_sub_assoc,Nat.add_assoc]

theorem emit_head (left : Bool) (s : RAMState) (e : SparseEntry) (out : Buffer)
    (hr : s.indices 10=out.coordinates) (hv : s.indices 11=out.coefficients)
    (ho : out.Safe)
    (he : Emit.head s (s.indices (Emit.rowRegister left))
      (s.indices (Emit.valueRegister left))=e) :
    Records out (Emit.advanced left s) [e] := by
  have hl : ∀j:ℕ,j<17→ out.coordinates≠j := by unfold Buffer.Safe at ho; omega
  have hl1 : ∀j:ℕ,j<17→ out.coordinates+1≠j := by unfold Buffer.Safe at ho; omega
  have hz : out.coefficients≠0 := by unfold Buffer.Safe at ho; omega
  cases left <;> simp [Emit.rowRegister,Emit.valueRegister] at he
  all_goals simp [Records,Emit.advanced,Emit.middle,Emit.rowRegister,Emit.valueRegister,
    Emit.countRegister,RAMState.setIndex,RAMState.setWord,hr,hv,he,hl,hl1]

end Maxwell.Cost.RealSparseOrder.Merge
