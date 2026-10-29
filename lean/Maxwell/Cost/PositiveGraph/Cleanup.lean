import Maxwell.Cost.PositiveGraph.Frame
import Maxwell.Cost.WordReset

namespace Maxwell.Cost.PositiveGraph.Cleanup
open Structured
open RationalAccumulator (Blank)

def code : Code := .seq (WordCall.resetStart 111)
  (.seq (WordCall.resetStart 112) (.call (TapeOps.clear 122)))

theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (row column shiftedColumn : List Bool) (s : Store)
    (h111 : s.val.tapes 111 = BitTape.shifted row 0)
    (h112 : s.val.tapes 112 = BitTape.shifted column 0)
    (h122 : BankArray.Word s.val 122 shiftedColumn) :
    ∃ t, Executes input randomTape code
        (11*(row.length+column.length)+6*shiftedColumn.length+24) s t ∧
      t.val.tapes 111 = BitTape.blank ∧ t.val.tapes 112 = BitTape.blank ∧ Blank t.val 122 ∧
      t.val.memory = s.val.memory ∧ Frame {111,112,122} s.val t.val ∧
      (∀ i, i ≠ 111 → i ≠ 112 → i ≠ 122 → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨origin,h122⟩ := h122
  obtain ⟨a,ea,atapes,af⟩ := WordCall.reset_start 111 input randomTape row 0 s h111
  obtain ⟨b,eb,btapes,bf⟩ := WordCall.reset_start 112 input randomTape column 0 a
    (by simpa [atapes] using h112)
  obtain ⟨t,et,ttapes,tf⟩ := WordCall.clear 122 input randomTape shiftedColumn origin b
    (by simpa [btapes,atapes] using h122)
  have fa : Frame {111,112,122} s.val a.val := Frame.of_transfer af (by
    intro i hi; simp_all)
  have fb : Frame {111,112,122} a.val b.val := Frame.of_transfer bf (by
    intro i hi; simp_all)
  have ft : Frame {111,112,122} b.val t.val := Frame.of_transfer (WordTransfer.frame_of_copy tf) (by
    intro i hi; simp_all)
  refine ⟨t,?_,by simp [ttapes,btapes,atapes,BitTape.blank],by simp [ttapes,btapes,BitTape.blank],
    ⟨origin+shiftedColumn.length,by simp [ttapes]⟩,
    tf.2.2.1.trans (bf.2.2.1.trans af.2.2.1),fa.trans (fb.trans ft),?_⟩
  · convert ea.seq (eb.seq et) using 1 <;> first | rfl | omega
  · intro i h1 h2 h3
    simp [ttapes,btapes,atapes,h1,h2,h3]

end Maxwell.Cost.PositiveGraph.Cleanup
