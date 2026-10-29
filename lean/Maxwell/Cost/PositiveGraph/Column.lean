import Maxwell.Cost.PositiveGraph.AddWords
import Maxwell.Cost.SourceCircuit.Common

namespace Maxwell.Cost.PositiveGraph.Column
open Structured
open RationalAccumulator (Blank)

def code : Code := .seq (.call (WordTransfer.clone 112 122)) (DecoderConstants.addCode 95 122)

/-- The right bipartite endpoint is computed from the retained dimension
and parsed column by actual binary addition. The parser words stay reusable. -/
theorem executes (input : List Bool) (randomTape : ℕ → Bool) (dimension column : List Bool)
    (s : Store) (hd : BankArray.Word s.val 95 dimension) (hc : BankArray.Word s.val 112 column)
    (h122 : Blank s.val 122) (hs : BankArray.Scratch s.val) :
    ∃ cost t, cost ≤ 200*dimension.length+215*column.length+817 ∧
      Executes input randomTape code cost s t ∧
      RationalAccumulator.Word t.val 122 (addressValue dimension+addressValue column) ∧
      BankArray.Scratch t.val ∧ t.val.memory = s.val.memory ∧
      SourceCircuit.Frame {122} s.val t.val ∧
      (∀ i, 4 ≤ i → i ≠ 122 → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨co,hco⟩ := hc
  obtain ⟨targetOrigin,hto⟩ := h122
  obtain ⟨a,ea,atapes,af⟩ := WordCall.clone 112 122 (by decide) input randomTape column co targetOrigin s hco hto
  have akeep (i : ℕ) (hi : i ≠ 122) : a.val.tapes i = s.val.tapes i := by simp [atapes,hi]
  have ascratch : BankArray.Scratch a.val := SourceCircuit.scratch_of_tapes hs (fun i hi => akeep i (by omega))
  have ab : ∀ i, i < 4 → Blank a.val i := by
    intro i hi
    interval_cases i
    · exact ascratch.1
    · exact ascratch.2.1
    · exact ascratch.2.2.1
    · exact ascratch.2.2.2.1
  obtain ⟨ac,t,acBound,et,tw,tb,tf⟩ := add_words 95 122 (by decide) (by decide) (by decide)
    input randomTape dimension column a (BankArray.word_of_eq (akeep 95 (by decide)) hd)
    ⟨targetOrigin,by simp [atapes]⟩ ab
  have keep (i : ℕ) (hi : 4 ≤ i) (h122i : i ≠ 122) : t.val.tapes i = s.val.tapes i :=
    (tf.2.2.2.2.2.1 i hi h122i).trans (akeep i h122i)
  refine ⟨_,t,by omega,ea.seq et,tw,?_,tf.2.2.1.trans af.2.2.1,?_,keep⟩
  · exact ⟨tb 0 (by decide),tb 1 (by decide),tb 2 (by decide),tb 3 (by decide),
      RationalAccumulator.blank_of_eq (keep 5 (by decide) (by decide)) hs.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 6 (by decide) (by decide)) hs.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 8 (by decide) (by decide)) hs.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 9 (by decide) (by decide)) hs.2.2.2.2.2.2.2⟩
  · refine ⟨tf.2.1.trans af.2.1,tf.2.2.2.1.trans af.2.2.2.1,
      tf.2.2.2.2.1.trans af.2.2.2.2.1,?_,?_,?_⟩
    · intro i hi hn
      exact keep i (by omega) (by simpa using hn)
    · exact (tf.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (af.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide))
    · intro i hi
      exact (tf.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (af.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega))

end Maxwell.Cost.PositiveGraph.Column
