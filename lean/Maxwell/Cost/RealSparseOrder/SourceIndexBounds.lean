import Maxwell.Cost.RealSparseOrder.SortResources
import Maxwell.Cost.RealSparseOrder.Initialize

namespace Maxwell.Cost.RealSparseOrder
open RealSimulation.Control RealSimulation.IndexWidth

theorem entryAt_bound {B : ℕ} {es : List SparseEntry}
    (h : ∀e∈es,e.row≤B ∧e.column≤B) (j : ℕ) :
    (RealSparse.entryAt es j).row≤B ∧(RealSparse.entryAt es j).column≤B := by
  unfold RealSparse.entryAt
  cases he : es[j]? with
  | none => simp
  | some e => simpa using h e (List.mem_of_getElem? he)

theorem source_input_bound {B : ℕ} (es : List SparseEntry) (vector : ℕ→ℝ)
    (hm : es.length≤B) (h : ∀e∈es,e.row≤B ∧e.column≤B) :
    InputBound B (RealSparse.input es vector) := by
  intro j
  simp only [RealSparse.input]
  split_ifs
  · exact hm
  · exact (entryAt_bound h _).1
  · exact (entryAt_bound h _).2

theorem Initialize.index_bound {B m : ℕ} {s : RAMState}
    (h : IndexBound B s) (hm : 100+2*m≤B) :
    IndexBound B (Initialize.initialized m s) := by
  unfold Initialize.initialized
  exact (((((((((h.setIndex 0 0 (by omega)).setIndex 1 1 (by omega)).setIndex 2 2 (by omega)).setIndex 18 1 (by omega)).setIndex 26 m (by omega)).setIndex 27 100 (by omega)).setIndex 28 100 (by omega)).setIndex 29 (m+m) (by omega)).setIndex 29 (m+m+100) (by omega)).setIndex 30 (m+100) (by omega)

theorem Initialize.bounded {B : ℕ} (es : List SparseEntry) (s : RAMState)
    (stored : Stored initialBuffer s es) (h : IndexBound B s) (hm : 100+4*es.length≤B) :
    Sort.Bounded B (Initialize.initialized es.length s) initialBuffer
      (Initialize.secondaryBuffer es.length) 1 (singletonRuns es) := by
  refine ⟨Initialize.invariant es s stored,Initialize.index_bound h (by omega),?_,?_,?_⟩
  · simp only [Within,initialBuffer,singletonRuns_flatten]
    constructor <;> omega
  · simp only [Within,Initialize.secondaryBuffer,singletonRuns_flatten]
    constructor <;> omega
  · simp only [singletonRuns_flatten]
    omega

/-- A polynomial natural-word cap gives an explicit logarithmic bit bound. -/
theorem size_le_polynomial {B A m k : ℕ} (h : B≤A*(m+2)^k) :
    B.size≤A.size+k*(m+2).size := by
  apply Nat.size_le.mpr
  have hp : (m+2)^k≤2^(k*(m+2).size) := by
    rw [Nat.mul_comm k,pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_size_self _)) k
  have hh := Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self A)
    (show 0<2^(k*(m+2).size) by positivity)
  rw [←pow_add] at hh
  exact (h.trans (Nat.mul_le_mul_left A hp)).trans_lt hh

end Maxwell.Cost.RealSparseOrder
