import Maxwell.Cost.PositiveGraph.PairWrite
import Maxwell.Cost.IncidenceEncoding

namespace Maxwell.Cost.PositiveGraph.Endpoints
open Structured
open RationalAccumulator (Blank)

def code : Code := .seq (PairWrite.code 118 111) (PairWrite.code 119 122)

def setPair {n : ℕ} (width index : ℕ) (hroom : index+1 < n)
    (first mediator : List Bool) (words : Vector (List Bool) n) : Vector (List Bool) n :=
  (words.set index (FixedWidth.bits width first) (by omega)).set
    (index+1) (FixedWidth.bits width mediator) hroom

def writePair (width index : ℕ) (first mediator : List Bool) (memory : ℕ → Bool) : ℕ → Bool :=
  MemoryWord.writeBits (MemoryWord.writeBits memory (index*width) (FixedWidth.bits width first))
    ((index+1)*width) (FixedWidth.bits width mediator)

theorem writePair_preserves {n m : ℕ} {memory : ℕ → Bool} {base arrayWidth : ℕ}
    {values : Vector (List Bool) n} (h : BitArray.Represents memory base arrayWidth values)
    (width index : ℕ) (hindex : index+1 < m) (first mediator : List Bool)
    (hsep : IncidenceEncoding.Separated base (n*arrayWidth) 0 (m*width)) :
    BitArray.Represents (writePair width index first mediator memory) base arrayWidth values := by
  have hfirst := IncidenceEncoding.represents_write_disjoint h 0 width ⟨index,by omega⟩
    (FixedWidth.bits width first) (FixedWidth.bits_length _ _) hsep
  have hsecond := IncidenceEncoding.represents_write_disjoint hfirst 0 width ⟨index+1,hindex⟩
    (FixedWidth.bits width mediator) (FixedWidth.bits_length _ _) hsep
  simpa only [writePair,zero_add] using hsecond

/-- One sparse matrix coefficient produces exactly two indexed positive
edges, with their four endpoint slots in the routing pass's flattened order. -/
theorem executes {n : ℕ} (input : List Bool) (randomTape : ℕ → Bool)
    (width clock row column mediator : List Bool) (left right : ℕ)
    (hl : left+1 < n) (hr : right+1 < n) (words : Vector (List Bool) n) (s : Store)
    (hwidth : 0 < width.length) (hpositive : 0 < addressValue width)
    (hclock : clock.length = addressValue width)
    (hrow : row.length ≤ addressValue width) (hcolumn : column.length ≤ addressValue width)
    (hmediator : mediator.length ≤ addressValue width)
    (hscratch : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (h140 : BankArray.Word s.val 140 width) (h146 : BankArray.Word s.val 146 clock)
    (h151 : BankArray.Word s.val 151 [])
    (h118 : BankArray.Word s.val 118 left.bits) (h119 : BankArray.Word s.val 119 right.bits)
    (h111 : BankArray.Word s.val 111 row) (h122 : BankArray.Word s.val 122 column)
    (h121 : BankArray.Word s.val 121 mediator)
    (harray : BitArray.Represents s.val.memory 0 (addressValue width) words) :
    ∃ cost t, cost ≤ PairWrite.price width left row mediator + PairWrite.price width right column mediator ∧
      Executes input randomTape code cost s t ∧
      t.val.memory = writePair (addressValue width) right column mediator
        (writePair (addressValue width) left row mediator s.val.memory) ∧
      BitArray.Represents t.val.memory 0 (addressValue width)
        (setPair (addressValue width) right hr column mediator
          (setPair (addressValue width) left hl row mediator words)) ∧
      BankArray.Word t.val 118 (left+2).bits ∧ BankArray.Word t.val 119 (right+2).bits ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 37 ∧
      SourceCircuit.Frame {37,118,119} s.val t.val := by
  obtain ⟨ac,a,acBound,ea,am,aa,a118,ascratch,a7,a37,af⟩ := PairWrite.executes 118 111
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    input randomTape width clock row mediator left hl words s hwidth hpositive hclock hrow hmediator
    hscratch h7 h37 h140 h118 h151 h146 h111 h121 harray
  have keep (j : ℕ) (hj : 10 ≤ j) (hj37 : j ≠ 37) (hj118 : j ≠ 118) :
      a.val.tapes j = s.val.tapes j := af.tapes j (Or.inr hj) (by simp [hj37,hj118])
  obtain ⟨bc,t,bcBound,et,tm,ta,t119,tscratch,t7,t37,tf⟩ := PairWrite.executes 119 122
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    input randomTape width clock column mediator right hr
    (setPair (addressValue width) left hl row mediator words) a hwidth hpositive hclock hcolumn hmediator
    ascratch a7 a37
    (BankArray.word_of_eq (keep 140 (by decide) (by decide) (by decide)) h140)
    (BankArray.word_of_eq (keep 119 (by decide) (by decide) (by decide)) h119)
    (BankArray.word_of_eq (keep 151 (by decide) (by decide) (by decide)) h151)
    (BankArray.word_of_eq (keep 146 (by decide) (by decide) (by decide)) h146)
    (BankArray.word_of_eq (keep 122 (by decide) (by decide) (by decide)) h122)
    (BankArray.word_of_eq (keep 121 (by decide) (by decide) (by decide)) h121) aa
  refine ⟨_,t,by omega,ea.seq et,?_,ta,
    BankArray.word_of_eq (tf.tapes 118 (Or.inr (by decide)) (by decide)) a118,
    t119,tscratch,t7,t37,af.mono (by decide) |>.trans (tf.mono (by decide))⟩
  exact tm.trans (congrArg (writePair (addressValue width) right column mediator) am)

end Maxwell.Cost.PositiveGraph.Endpoints
