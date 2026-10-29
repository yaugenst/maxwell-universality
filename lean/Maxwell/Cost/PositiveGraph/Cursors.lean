import Maxwell.Cost.PositiveGraph.Protocol
import Maxwell.Cost.WordCall

namespace Maxwell.Cost.PositiveGraph.InitializeCursors
open Structured
open RationalAccumulator (Blank)

def code : Code := .seq (.call (WordTransfer.clone 153 119)) (.call (WordTransfer.clone 154 121))

theorem executes (input : List Bool) (randomTape : ℕ → Bool) (dimension count : ℕ) (s : Store)
    (h153 : BankArray.Word s.val 153 (2*count).bits) (h154 : BankArray.Word s.val 154 (2*dimension).bits)
    (h118 : Blank s.val 118) (h119 : Blank s.val 119) (h121 : Blank s.val 121) :
    ∃ t, Executes input randomTape code
        (15*((2*count).bits.length+(2*dimension).bits.length)+34) s t ∧
      Cursors dimension count 0 t.val ∧ t.val.memory = s.val.memory ∧
      Frame {119,121} s.val t.val ∧
      (∀ i, i ≠ 119 → i ≠ 121 → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨countOrigin,h153⟩ := h153
  obtain ⟨dimensionOrigin,h154⟩ := h154
  obtain ⟨rightOrigin,h119⟩ := h119
  obtain ⟨mediatorOrigin,h121⟩ := h121
  obtain ⟨a,ea,atapes,af⟩ := WordCall.clone 153 119 (by decide) input randomTape
    (2*count).bits countOrigin rightOrigin s h153 h119
  obtain ⟨t,et,ttapes,tf⟩ := WordCall.clone 154 121 (by decide) input randomTape
    (2*dimension).bits dimensionOrigin mediatorOrigin a (by simpa [atapes] using h154)
    (by simpa [atapes] using h121)
  have keep (i : ℕ) (hi : i ≠ 119) (hj : i ≠ 121) : t.val.tapes i = s.val.tapes i := by
    simp [ttapes,atapes,hi,hj]
  refine ⟨t,?_,?_,tf.2.2.1.trans af.2.2.1,?_,keep⟩
  · convert ea.seq et using 1 <;> first | rfl | omega
  · refine ⟨?_,⟨rightOrigin,by simp [ttapes,atapes]⟩,⟨mediatorOrigin,by simp [ttapes]⟩⟩
    obtain ⟨origin,ho⟩ := h118
    exact ⟨origin,by simpa [BitTape.shifted,BitTape.blank] using (keep 118 (by decide) (by decide)).trans ho⟩
  · exact (Frame.of_transfer af (by intro i hi; simp_all)).trans
      (Frame.of_transfer tf (by intro i hi; simp_all))

end Maxwell.Cost.PositiveGraph.InitializeCursors
