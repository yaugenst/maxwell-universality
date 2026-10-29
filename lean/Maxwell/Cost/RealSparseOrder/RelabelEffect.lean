import Maxwell.Cost.RealSparseOrder.RelabelStep

namespace Maxwell.Cost.RealSparseOrder.Relabel
open RealSimulation.Control

set_option maxHeartbeats 800000 in
theorem processed_indices {input : RAMInput} {s : Store} {b : Buffer} {remaining : ℕ}
    {previous : Option ℕ} {count m map rhs row : ℕ}
    (h : Config s.val b remaining previous count m map rhs)
    (hm : 100≤map) (hr : s.val.indices b.coordinates=row)
    (j : ℕ) (hj : 100≤j) :
    (processed input previous row s).val.indices j=
      if j=b.coordinates then nextCount previous count row-1 else
        if previous≠some row ∧j=map+count then row else s.val.indices j := by
  have hd : ∀i:ℕ,i<42→i≠map+count := by omega
  have hjc : ∀i:ℕ,i<42→j≠i := by omega
  by_cases he : previous=some row
  · simp [processed,chosen,he,nextCount,loaded,rewritten,Store.ofState,RAMState.setIndex,
      h.count,h.cursor,hjc,Function.update_apply]
  · simp [processed,chosen,he,nextCount,loaded,created,rewritten,Store.ofState,
      RAMState.setIndex,RAMState.setWord,h.count,h.cursor,h.mapBase,h.rhsBase,
      hr,hd,hjc,Function.update_apply]

set_option maxHeartbeats 800000 in
theorem processed_words {input : RAMInput} {s : Store} {b : Buffer} {remaining : ℕ}
    {previous : Option ℕ} {count m map rhs row : ℕ}
    (h : Config s.val b remaining previous count m map rhs)
    (hm : 100≤map) (hr : s.val.indices b.coordinates=row) (j : ℕ) (hj : 1≤j) :
    (processed input previous row s).val.words j=
      if previous≠some row ∧j=rhs+count then input.words (m+row) else s.val.words j := by
  have hd : ∀i:ℕ,i<42→i≠map+count := by omega
  by_cases he : previous=some row
  · simp [processed,chosen,he,loaded,rewritten,Store.ofState,RAMState.setIndex]
  · simp [processed,chosen,he,loaded,created,rewritten,Store.ofState,
      RAMState.setIndex,RAMState.setWord,h.count,h.cursor,h.mapBase,h.rhsBase,
      h.originalCount,hr,hd,show j≠0 by omega,Function.update_apply]

theorem processed_channels (input : RAMInput) (previous : Option ℕ) (row : ℕ) (s : Store) :
    (processed input previous row s).val.randomCursor=s.val.randomCursor ∧
    (processed input previous row s).val.output=s.val.output ∧
    (processed input previous row s).val.indexOutput=s.val.indexOutput := by
  by_cases he : previous=some row <;>
    simp [processed,chosen,he,loaded,created,rewritten,Store.ofState,RAMState.setIndex,RAMState.setWord]

end Maxwell.Cost.RealSparseOrder.Relabel
