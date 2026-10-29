import Maxwell.Cost.IncidencePass.Common
import Maxwell.Cost.BankArray.Increment

namespace Maxwell.Cost.IncidencePass
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)

def counterCode : Code := .seq (.call (WordTransfer.clone 89 90)) (BankArray.incrementCode 90)

/-- Preserve the two-bit rank while incrementing a private copy for the
counter update. The degree-three invariant guarantees that two bits suffice. -/
theorem counter_executes (input : List Bool) (tape : ℕ → Bool) (rank : ℕ) (hrank : rank < 3)
    (s : Store) (h89 : Word s.val 89 (IncidenceEncoding.word 2 rank))
    (h90 : Blank s.val 90) (hscratch : BankArray.Scratch s.val) :
    ∃ cost t, cost ≤ 89 ∧ Executes input tape counterCode cost s t ∧
      Word t.val 90 (IncidenceEncoding.word 2 (rank + 1)) ∧ BankArray.Scratch t.val ∧
      t.val.memory = s.val.memory ∧
      (∀ i, i ≠ 90 → t.val.tapes i = s.val.tapes i) ∧ Frame s.val t.val := by
  obtain ⟨ro, hr⟩ := h89
  obtain ⟨so, hs⟩ := h90
  obtain ⟨c, ec, hc, fc⟩ := WordCall.clone 89 90 (by omega) input tape
    (IncidenceEncoding.word 2 rank) ro so s hr hs
  have cs : BankArray.Scratch c.val := by
    have keep (i : ℕ) (hi : i < 10) : c.val.tapes i = s.val.tapes i := by
      simp [hc, show i ≠ 90 by omega]
    rcases hscratch with ⟨h0, h1, h2, h3, h5, h6, h8, h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (keep 0 (by omega)) h0,
      RationalAccumulator.blank_of_eq (keep 1 (by omega)) h1,
      RationalAccumulator.blank_of_eq (keep 2 (by omega)) h2,
      RationalAccumulator.blank_of_eq (keep 3 (by omega)) h3,
      RationalAccumulator.blank_of_eq (keep 5 (by omega)) h5,
      RationalAccumulator.blank_of_eq (keep 6 (by omega)) h6,
      RationalAccumulator.blank_of_eq (keep 8 (by omega)) h8,
      RationalAccumulator.blank_of_eq (keep 9 (by omega)) h9⟩
  obtain ⟨cost, t, hcost, et, ht, hts, htm, _, hkeep, ft⟩ :=
    BankArray.increment_bank 90 (by omega) input tape (IncidenceEncoding.word 2 rank) c
      ⟨so, by simp [hc]⟩ cs
  refine ⟨15 * (IncidenceEncoding.word 2 rank).length + 17 + cost, t, ?_, ec.seq et,
    ?_, hts, htm.trans fc.2.2.1, ?_,
    (Frame.of_transfer (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) fc).trans
      (Frame.of_except (Or.inr (Or.inr rfl)) ft)⟩
  · simp only [IncidenceEncoding.word_length] at hcost ⊢
    omega
  · simpa only [IncidenceEncoding.word, BankArray.increment_two_bits rank hrank] using ht
  · intro i hi
    rw [hkeep i hi, hc]
    simp [hi]

end Maxwell.Cost.IncidencePass
