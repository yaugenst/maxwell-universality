import Maxwell.Cost.RealSparseOrder.RelabelFrame

namespace Maxwell.Cost.RealSparseOrder.Relabel
open RealSimulation.Control

theorem processed_records {input : RAMInput} {s : Store} {b : Buffer} {previous : Option ℕ}
    {count m map rhs : ℕ} {e : SparseEntry} {es : List SparseEntry}
    (h : Config s.val b (es.length+1) previous count m map rhs)
    (hb : b.Safe) (hm : b.coordinates+2*(es.length+1)≤map)
    (hv : b.coefficients+(es.length+1)≤rhs) (hs : Records b s.val (e::es)) :
    Records b (processed input previous e.row s).val
      ({e with row:=nextCount previous count e.row-1}::es) := by
  have hmap : 100≤map := by have hh := hb.2; omega
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [ite_true] using processed_indices h hmap hs.1 b.coordinates hb.2
  · rw [processed_indices h hmap hs.1 (b.coordinates+1) (by have hh:=hb.2; omega)]
    simp only [show b.coordinates+1≠b.coordinates by omega,ite_false,
      show b.coordinates+1≠map+count by omega,and_false]
    exact hs.2.1
  · rw [processed_words h hmap hs.1 b.coefficients (by have hh:=hb.1; omega)]
    simp only [show b.coefficients≠rhs+count by omega,and_false,ite_false]
    exact hs.2.2.1
  · apply Records.congr_intervals hs.2.2.2
    · intro j hj hl
      simp only [Buffer.shift] at hj hl
      rw [processed_indices h hmap hs.1 j (by have hh:=hb.2; omega)]
      simp [show j≠b.coordinates by omega,show j≠map+count by omega]
    · intro j hj hl
      simp only [Buffer.shift] at hj hl
      rw [processed_words h hmap hs.1 j (by have hh:=hb.1; omega)]
      simp [show j≠rhs+count by omega]

theorem processed_gathered {input : RAMInput} {s : Store} {b : Buffer} {previous : Option ℕ}
    {remaining count m map rhs : ℕ} {row : ℕ} (vector : ℕ→ℝ)
    (h : Config s.val b remaining previous count m map rhs)
    (hb : b.Safe) (hm : b.coordinates+2≤map) (hv : 100≤rhs)
    (hr : s.val.indices b.coordinates=row) (hne : previous≠some row)
    (hin : input.words (m+row)=vector row) :
    Gathered (map+count) (rhs+count) (processed input previous row s).val vector [row] := by
  have hmap : 100≤map := by have hh:=hb.2; omega
  refine ⟨?_,?_,trivial⟩
  · rw [processed_indices h hmap hr (map+count) (by omega)]
    simp [show map+count≠b.coordinates by omega,hne]
  · rw [processed_words h hmap hr (rhs+count) (by omega)]
    simpa [hne] using hin

end Maxwell.Cost.RealSparseOrder.Relabel
