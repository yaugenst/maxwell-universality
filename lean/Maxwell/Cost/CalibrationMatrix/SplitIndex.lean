import Maxwell.Cost.CalibrationMatrix.EntryPrepared
import Maxwell.Cost.CalibrationMatrix.HeaderWords

/-! Actual quotient/remainder extraction for a row-major matrix cursor. -/
namespace Maxwell.Cost.CalibrationMatrix.SplitIndex
open Structured
open RationalAccumulator (Blank blank_of_eq)

def changes : Finset ℕ := {0,1,2,3,4,72,123,124}

def code (radixBank indexBank : ℕ) : Code :=
  .seq (Entry.prepareCode radixBank indexBank)
    (.seq (Entry.digitCode 72)
      (.seq (.call (Rewind.program 3))
        (.seq (.call (WordTransfer.move 3 123))
          (.seq (.call (WordTransfer.move 72 124)) (.call (TapeOps.clear 1))))))

theorem executes (radixBank indexBank : ℕ) (hrb : 100 ≤ radixBank) (hib : 100 ≤ indexBank)
    (input : List Bool) (tape : ℕ → Bool) (radix index : List Bool)
    (hpositive : 0 < addressValue radix) (s : Store)
    (hr : BankArray.Word s.val radixBank radix) (hi : BankArray.Word s.val indexBank index)
    (hs : ∀ i, i < 5 → Blank s.val i) (h72 : Blank s.val 72)
    (h123 : Blank s.val 123) (h124 : Blank s.val 124) :
    ∃ cost t row column, cost ≤ 700*(radix.length+index.length+3)^2 ∧
      Executes input tape (code radixBank indexBank) cost s t ∧
      BankArray.Word t.val 123 row ∧ BankArray.Word t.val 124 column ∧
      addressValue row = addressValue index / addressValue radix ∧
      addressValue column = addressValue index % addressValue radix ∧
      row.length = index.length ∧ column.length ≤ radix.length+index.length ∧
      (∀ i, i < 5 → Blank t.val i) ∧ Blank t.val 72 ∧
      BinaryPrecision.Frame changes s.val t.val := by
  obtain ⟨ro,hr⟩ := hr
  obtain ⟨io,hi⟩ := hi
  obtain ⟨a,ea,hp,fa⟩ := Entry.prepare radixBank indexBank (by omega) (by omega) input tape radix index
    ro io s hr hi hs
  obtain ⟨dc,b,column,row,hdc,eb,hb,hw,hvcol,hvrow,hlcol,hlrow,fb⟩ :=
    Entry.digit 72 (by decide) input tape radix index hpositive a hp
      (fa.blank (by simp) h72)
  obtain ⟨h0,h1,h2,⟨qo,hq⟩,h4⟩ := hb
  obtain ⟨mo,hm⟩ := hw
  obtain ⟨c,ec,hc,fc⟩ := HeaderWords.rewind 3 input tape row qo b hq
  have prep : BinaryPrecision.Frame changes s.val a.val := fa.mono (by
    intro i hi; simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [changes])
  have digit : BinaryPrecision.Frame changes a.val b.val := by
    refine ⟨fb.1,fb.2.1,fb.2.2.1,fb.2.2.2.1,fb.2.2.2.2.1,?_⟩
    intro i hi
    simp only [changes,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    exact fb.2.2.2.2.2.1 i (by omega) (by tauto)
  have rewind : BinaryPrecision.Frame changes b.val c.val := fc.mono (by simp [changes])
  have pre123 : Blank c.val 123 := by
    apply fc.blank (by simp)
    apply blank_of_eq (fb.2.2.2.2.2.1 123 (by decide) (by decide))
    exact fa.blank (by simp) h123
  obtain ⟨o123,ho123⟩ := pre123
  obtain ⟨d,ed,dtapes,fd,_⟩ := move_word 3 123 (by decide) input tape row qo o123 c hc ho123
  have dc72 : c.val.tapes 72 = BitTape.shifted column mo := (fc.tapes 72 (by simp)).trans hm
  have d72 : d.val.tapes 72 = BitTape.shifted column mo := by simpa [dtapes] using dc72
  have d124 : Blank d.val 124 := by
    apply fd.blank (by simp)
    apply fc.blank (by simp)
    apply blank_of_eq (fb.2.2.2.2.2.1 124 (by decide) (by decide))
    exact fa.blank (by simp) h124
  obtain ⟨o124,ho124⟩ := d124
  obtain ⟨e,ee,etapes,fe,_⟩ := move_word 72 124 (by decide) input tape column mo o124 d d72 ho124
  have e1 : BankArray.Word e.val 1 radix :=
    fe.word (by simp) (fd.word (by simp) (fc.word (by simp) h1))
  obtain ⟨t,et,ht1,ft⟩ := HeaderWords.clear 1 input tape radix e e1
  have fd' : BinaryPrecision.Frame changes c.val d.val := fd.mono (by decide)
  have fe' : BinaryPrecision.Frame changes d.val e.val := fe.mono (by decide)
  have ft' : BinaryPrecision.Frame changes e.val t.val := ft.mono (by simp [changes])
  refine ⟨15*radix.length+20*index.length+38+
      (dc+(4*row.length+6+(12*row.length+11+(12*column.length+11+(6*radix.length+4))))),
    t,row,column,?_,ea.seq (eb.seq (ec.seq (ed.seq (ee.seq et)))),?_,?_,hvrow,hvcol,hlrow,hlcol,?_,?_,
    (((prep.trans digit).trans rewind).trans fd').trans (fe'.trans ft')⟩
  · rw [hlrow]
    nlinarith
  · apply ft.word (by simp)
    apply fe.word (by simp)
    exact ⟨o123,by simp [dtapes]⟩
  · apply ft.word (by simp)
    exact ⟨o124,by simp [etapes]⟩
  · intro i hi
    interval_cases i
    · exact ft.blank (by simp) (fe.blank (by simp) (fd.blank (by simp) (fc.blank (by simp) h0)))
    · exact ht1
    · exact ft.blank (by simp) (fe.blank (by simp) (fd.blank (by simp) (fc.blank (by simp) h2)))
    · apply ft.blank (by simp)
      apply fe.blank (by simp)
      exact ⟨qo+row.length,by simp [dtapes]⟩
    · exact ft.blank (by simp) (fe.blank (by simp) (fd.blank (by simp) (fc.blank (by simp) h4)))
  · apply ft.blank (by simp)
    exact ⟨mo+column.length,by simp [etapes]⟩

end Maxwell.Cost.CalibrationMatrix.SplitIndex
