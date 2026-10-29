import Maxwell.Cost.RealSparseOrder.ColumnMaxOps

namespace Maxwell.Cost.RealSparseOrder.ColumnMax
open RealSimulation.Control

structure Config (s : RAMState) (b : Buffer) (remaining acc : ℕ) : Prop where
  one : s.indices 1=1
  two : s.indices 2=2
  remaining : s.indices 43=remaining
  cursor : s.indices 44=b.coordinates+1
  maximum : s.indices 42=acc

@[simp] theorem config_ofState (s : RAMState) (b : Buffer) (remaining acc : ℕ) :
    Config (Store.ofState s).val b remaining acc ↔Config s b remaining acc := by
  constructor <;> intro h <;> exact ⟨h.one,h.two,h.remaining,h.cursor,h.maximum⟩

theorem processed_config {s : Store} {b : Buffer} {remaining acc column : ℕ}
    (h : Config s.val b remaining acc) (hc : s.val.indices (b.coordinates+1)=column) :
    Config (processed s).val (b.shift 1) (remaining-1) (max acc (column+1)) := by
  constructor
  · exact (processed_frame s 1 (Or.inl (by decide))).trans h.one
  · exact (processed_frame s 2 (Or.inl (by decide))).trans h.two
  · simp [processed,advanced,Store.ofState,RAMState.setIndex,
      chosen_frame _ 43 (by decide),loaded,h.remaining]
  · simp [processed,advanced,Store.ofState,RAMState.setIndex,
      chosen_frame _ 44 (by decide),loaded,h.cursor,Buffer.shift,Nat.add_assoc,Nat.add_comm]
    omega
  · change (advanced (chosen (Store.ofState (loaded s.val))).val).indices 42=_
    simp only [advanced,RAMState.setIndex,Function.update_of_ne (by decide : (42 : ℕ)≠43),
      Function.update_of_ne (by decide : (42 : ℕ)≠44)]
    rw [chosen_max]
    simp [loaded,Store.ofState,RAMState.setIndex,h.cursor,h.maximum,hc]

theorem records_processed {s : Store} {b : Buffer} {es : List SparseEntry}
    (h : Records b s.val es) (hb : b.Safe) : Records b (processed s).val es := by
  induction es generalizing b with
  | nil => trivial
  | cons e es ih =>
    refine ⟨(processed_frame s b.coordinates (Or.inr (by have hh:=hb.2; omega))).trans h.1,
      (processed_frame s (b.coordinates+1) (Or.inr (by have hh:=hb.2; omega))).trans h.2.1,?_,
      ih h.2.2.2 (hb.shift 1)⟩
    rw [processed_words]
    exact h.2.2.1

end Maxwell.Cost.RealSparseOrder.ColumnMax
