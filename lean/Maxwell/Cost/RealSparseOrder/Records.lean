import Maxwell.Cost.RealSparseOrder.Memory

namespace Maxwell.Cost.RealSparseOrder

theorem records_append (b : Buffer) (s : RAMState) (xs ys : List SparseEntry) :
    Records b s (xs++ys) ↔Records b s xs ∧Records (b.shift xs.length) s ys := by
  induction xs generalizing b with
  | nil => simp [Records]
  | cons e xs ih =>
    simp only [List.cons_append,Records,ih,List.length_cons,Buffer.shift_shift]
    rw [show 1+xs.length=xs.length+1 by omega]
    tauto

theorem records_take_drop {b : Buffer} {s : RAMState} {es : List SparseEntry}
    (h : Records b s es) (n : ℕ) :
    Records b s (es.take n) ∧Records (b.shift (min n es.length)) s (es.drop n) := by
  have hh := (records_append b s (es.take n) (es.drop n)).mp (by simpa using h)
  simpa only [List.length_take] using hh

theorem records_eq_memory {b : Buffer} {s t : RAMState} {es : List SparseEntry}
    (h : Records b s es) (hidx : t.indices=s.indices) (hwords : t.words=s.words) :
    Records b t es := by
  rw [records_stored] at h ⊢
  intro i hi
  simpa only [hidx,hwords] using h i hi

theorem MemoryFrame.ofState {b : Buffer} {n : ℕ} {s t : RAMState}
    (h : MemoryFrame b n s t) :
    MemoryFrame b n s (RealSimulation.Control.Store.ofState t).val := h

end Maxwell.Cost.RealSparseOrder
