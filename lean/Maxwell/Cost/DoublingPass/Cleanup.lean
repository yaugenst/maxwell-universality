import Maxwell.Cost.DoublingPass.Common

namespace Maxwell.Cost.DoublingPass
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)

def cleanupCode : Code := .seq (.call (TapeOps.clear 88))
  (.seq (.call (TapeOps.clear 89)) (.seq (.call (TapeOps.clear 90))
    (.seq (.call (TapeOps.clear 91)) (.call (TapeOps.clear 92)))))

theorem cleanup_executes (input : List Bool) (tape : ℕ → Bool)
    (aWord bWord cWord dWord eWord : List Bool) (s : Store)
    (h88 : Word s.val 88 aWord) (h89 : Word s.val 89 bWord) (h90 : Word s.val 90 cWord)
    (h91 : Word s.val 91 dWord) (h92 : Word s.val 92 eWord)
    (scratch : BankArray.Scratch s.val) (empty7 : Blank s.val 7) :
    ∃ t, Executes input tape cleanupCode
        (6 * (aWord.length + bWord.length + cWord.length + dWord.length + eWord.length) + 20) s t ∧
      Workspace t.val ∧ t.val.memory = s.val.memory ∧ Frame s.val t.val := by
  obtain ⟨ao, h88⟩ := h88
  obtain ⟨bo, h89⟩ := h89
  obtain ⟨co, h90⟩ := h90
  obtain ⟨dOrigin, h91⟩ := h91
  obtain ⟨eo, h92⟩ := h92
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clear 88 input tape aWord ao s h88
  obtain ⟨b, eb, hb, fb⟩ := WordCall.clear 89 input tape bWord bo a (by simpa [ha] using h89)
  obtain ⟨c, ec, hc, fc⟩ := WordCall.clear 90 input tape cWord co b (by simpa [hb, ha] using h90)
  obtain ⟨d, ed, hd, fd⟩ := WordCall.clear 91 input tape dWord dOrigin c (by simpa [hc, hb, ha] using h91)
  obtain ⟨t, et, ht, ft⟩ := WordCall.clear 92 input tape eWord eo d (by simpa [hd, hc, hb, ha] using h92)
  have hglobal : t.val.tapes = Function.update (Function.update (Function.update (Function.update (Function.update (s.val.tapes) 88 {BitTape.blank with head := ao + aWord.length}) 89 {BitTape.blank with head := bo + bWord.length}) 90 {BitTape.blank with head := co + cWord.length}) 91 {BitTape.blank with head := dOrigin + dWord.length}) 92 {BitTape.blank with head := eo + eWord.length} := by rw [ht, hd, hc, hb, ha]
  have keep (j : ℕ) (hj : j < 10) : t.val.tapes j = s.val.tapes j := by
    simp [hglobal, show j ≠ 88 by omega, show j ≠ 89 by omega, show j ≠ 90 by omega,
      show j ≠ 91 by omega, show j ≠ 92 by omega]
  have ts : BankArray.Scratch t.val := by
    rcases scratch with ⟨h0, h1, h2, h3, h5, h6, h8, h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (keep 0 (by omega)) h0,
      RationalAccumulator.blank_of_eq (keep 1 (by omega)) h1,
      RationalAccumulator.blank_of_eq (keep 2 (by omega)) h2,
      RationalAccumulator.blank_of_eq (keep 3 (by omega)) h3,
      RationalAccumulator.blank_of_eq (keep 5 (by omega)) h5,
      RationalAccumulator.blank_of_eq (keep 6 (by omega)) h6,
      RationalAccumulator.blank_of_eq (keep 8 (by omega)) h8,
      RationalAccumulator.blank_of_eq (keep 9 (by omega)) h9⟩
  refine ⟨t, ?_, ⟨ts, RationalAccumulator.blank_of_eq (keep 7 (by omega)) empty7, ?_⟩,
    ft.2.2.1.trans (fd.2.2.1.trans (fc.2.2.1.trans (fb.2.2.1.trans fa.2.2.1))), ?_⟩
  · convert ea.seq (eb.seq (ec.seq (ed.seq et))) using 1 <;> first | rfl | omega
  · intro j hj
    dsimp [Private] at hj
    have cases : j = 88 ∨ j = 89 ∨ j = 90 ∨ j = 91 ∨ j = 92 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl
    · exact ⟨ao + aWord.length, by simp [hglobal]⟩
    · exact ⟨bo + bWord.length, by simp [hglobal]⟩
    · exact ⟨co + cWord.length, by simp [hglobal]⟩
    · exact ⟨dOrigin + dWord.length, by simp [hglobal]⟩
    · exact ⟨eo + eWord.length, by simp [hglobal]⟩
  · exact (Frame.of_clear (by simp [Private]) fa).trans
      ((Frame.of_clear (by simp [Private]) fb).trans
        ((Frame.of_clear (by simp [Private]) fc).trans
          ((Frame.of_clear (by simp [Private]) fd).trans (Frame.of_clear (by simp [Private]) ft))))

end Maxwell.Cost.DoublingPass
