import Maxwell.Cost.DecoderParser.Rows

namespace Maxwell.Cost.DecoderParser

/-- Exact emitted row pairs satisfy the public decoder output contract,
including the actual canonical framing and unreduced numerator widths. -/
theorem rows_represents {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (w : D.Messages) (A : ℕ) (pairs : List Codec.RationalPair)
    (h : List.Forall₂ (RowResult D w A) (rows D) pairs) :
    Codec.RepresentsOutput (A+2) (D.decode w)
      (Codec.nat n++pairs.flatMap Codec.RationalPair.encode) := by
  have hlen : pairs.length=n := h.length_eq.symm.trans (rows_length D)
  let output : Fin n → Codec.RationalPair := fun i => pairs.get ⟨i.val,by rw [hlen];exact i.isLt⟩
  have hout : List.ofFn output=pairs := by
    apply List.ext_getElem
    · simpa using hlen.symm
    · intro i hi hj
      simp [output]
  refine ⟨output,by simp [Codec.list,hout,hlen],?_,?_⟩
  · intro i
    have hi := h.get (i := i.val) (by simp) (by rw [hlen];exact i.isLt)
    change RowResult D w A ((rows D).get ⟨i.val,_⟩) (output i) at hi
    have hr : (rows D).get ⟨i.val,by simp⟩=(D.offset i,rowTerms D i) := by
      simp [rows]
    rw [hr] at hi
    exact hi.1.trans (rowTerms_value D w i)
  · intro i
    have hi := h.get (i := i.val) (by simp) (by rw [hlen];exact i.isLt)
    exact hi.2

end Maxwell.Cost.DecoderParser
