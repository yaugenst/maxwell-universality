import Maxwell.Cost.Structured.WordDifference
import Maxwell.Cost.Structured.NatAssign.Values

/-! Nonnegative subtraction within an arbitrary retained natural-word bank. -/
namespace Maxwell.Cost.Structured.NatAssign

theorem difference_executes (ids : Finset ℕ) (left right target B : ℕ)
    (lower : ∀i∈ids,4 ≤ i) (hl : left∈ids) (hr : right∈ids) (ht : target∈ids)
    (v : ℕ→ℕ) (ordered : v right≤v left) (zero : v target=0)
    (width : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : Bank ids v s.val) (scratch : Scratch s.val) :
    ∃cost t,Executes input tape (WordDifference.code left right target) cost s t ∧
      cost≤300*(2*B+4) ∧ Bank ids (Function.update v target (v left-v right)) t.val ∧
      Scratch t.val ∧ (∀i∈ids,((Function.update v target (v left-v right)) i).bits.length≤B) ∧
      BinaryPrecision.Frame {0,1,2,target} s.val t.val := by
  have blank : RationalAccumulator.Blank s.val target := by
    apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    simpa only [zero] using bank target ht
  obtain ⟨cost,t,execution,bound,word,st,frame⟩ := WordDifference.executes left right target
    (lower left hl) (lower right hr) (lower target ht) input tape (v left) (v right) ordered
    s (bank left hl) (bank right hr) blank scratch
  refine ⟨cost,t,execution,bound.trans (Nat.mul_le_mul_left _ (by
    have := width left hl;have := width right hr;omega)),?_,st,?_,frame⟩
  · intro i hi
    by_cases same : i=target
    · subst i;simpa only [Function.update_self] using word
    · have outside : i∉({0,1,2,target}:Finset ℕ) := by
        simp;have := lower i hi;omega
      simpa only [Function.update_of_ne same] using
        RationalAccumulator.word_of_eq (frame.tapes i outside) (bank i hi)
  · intro i hi
    by_cases same : i=target
    · subst i
      simp only [Function.update_self]
      have smaller := Nat.size_le_size (Nat.sub_le (v left) (v right))
      rw [←Nat.size_eq_bits_len,←Nat.size_eq_bits_len] at smaller
      exact smaller.trans (width left hl)
    · simpa only [Function.update_of_ne same] using width i hi

#print axioms difference_executes
end Maxwell.Cost.Structured.NatAssign
