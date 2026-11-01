import Maxwell.Cost.Array

/-! An array view may change its finite index type while retaining the
same numeric indices and stored words. -/

namespace Maxwell.Cost.BitArray

theorem Represents.reindex {n m base width : ℕ} {memory : ℕ→Bool}
    {xs : Vector (List Bool) n} (h : Represents memory base width xs)
    (ys : Vector (List Bool) m) (index : Fin m→Fin n)
    (sameIndex : ∀i,(index i).val=i.val) (sameWord : ∀i,ys.get i=xs.get (index i)) :
    Represents memory base width ys := by
  have lengths (i : Fin m) : (ys.get i).length=width := by rw [sameWord];exact h.length _
  refine ⟨lengths,?_⟩
  intro i j hj
  have he := h.bits (index i) j hj
  simpa only [sameIndex,sameWord] using he

#print axioms Represents.reindex

end Maxwell.Cost.BitArray
