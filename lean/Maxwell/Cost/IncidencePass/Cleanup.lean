import Maxwell.Cost.IncidencePass.Common

namespace Maxwell.Cost.IncidencePass
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)

def cleanupCode : Code := .seq (.call (TapeOps.clear 88))
  (.seq (.call (TapeOps.clear 89)) (.call (TapeOps.clear 90)))

theorem cleanup_executes (input : List Bool) (tape : ℕ → Bool)
    (vertex rank incremented : List Bool) (s : Store)
    (h88 : Word s.val 88 vertex) (h89 : Word s.val 89 rank) (h90 : Word s.val 90 incremented)
    (hs : BankArray.Scratch s.val) (h7 : Blank s.val 7) :
    ∃ t, Executes input tape cleanupCode
        (6 * (vertex.length + rank.length + incremented.length) + 12) s t ∧
      Workspace t.val ∧ t.val.memory = s.val.memory ∧ Frame s.val t.val := by
  obtain ⟨vo, hv⟩ := h88
  obtain ⟨ro, hr⟩ := h89
  obtain ⟨io, hi⟩ := h90
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clear 88 input tape vertex vo s hv
  obtain ⟨b, eb, hb, fb⟩ := WordCall.clear 89 input tape rank ro a (by simpa [ha] using hr)
  obtain ⟨t, et, ht, ft⟩ := WordCall.clear 90 input tape incremented io b (by simpa [hb, ha] using hi)
  have hglobal : t.val.tapes = Function.update (Function.update (Function.update s.val.tapes
      88 {BitTape.blank with head := vo + vertex.length})
      89 {BitTape.blank with head := ro + rank.length})
      90 {BitTape.blank with head := io + incremented.length} := by rw [ht, hb, ha]
  have keep (j : ℕ) (hj : j < 10) : t.val.tapes j = s.val.tapes j := by
    simp [hglobal, show j ≠ 88 by omega, show j ≠ 89 by omega, show j ≠ 90 by omega]
  have ts : BankArray.Scratch t.val := by
    rcases hs with ⟨h0, h1, h2, h3, h5, h6, h8, h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (keep 0 (by omega)) h0,
      RationalAccumulator.blank_of_eq (keep 1 (by omega)) h1,
      RationalAccumulator.blank_of_eq (keep 2 (by omega)) h2,
      RationalAccumulator.blank_of_eq (keep 3 (by omega)) h3,
      RationalAccumulator.blank_of_eq (keep 5 (by omega)) h5,
      RationalAccumulator.blank_of_eq (keep 6 (by omega)) h6,
      RationalAccumulator.blank_of_eq (keep 8 (by omega)) h8,
      RationalAccumulator.blank_of_eq (keep 9 (by omega)) h9⟩
  refine ⟨t, ?_, ⟨ts, RationalAccumulator.blank_of_eq (keep 7 (by omega)) h7,
    ⟨vo + vertex.length, by simp [hglobal]⟩, ⟨ro + rank.length, by simp [hglobal]⟩,
    ⟨io + incremented.length, by simp [hglobal]⟩⟩,
    ft.2.2.1.trans (fb.2.2.1.trans fa.2.2.1), ?_⟩
  · convert ea.seq (eb.seq et) using 1 <;> first | rfl | omega
  · exact (Frame.of_transfer (Or.inl rfl) (Or.inl rfl) (WordTransfer.frame_of_copy fa)).trans
      ((Frame.of_transfer (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl)) (WordTransfer.frame_of_copy fb)).trans
        (Frame.of_transfer (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl)) (WordTransfer.frame_of_copy ft)))

end Maxwell.Cost.IncidencePass
