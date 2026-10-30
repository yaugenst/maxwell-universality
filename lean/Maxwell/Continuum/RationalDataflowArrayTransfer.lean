import Maxwell.Continuum.RationalDataflowArrayOutputFrame

/-! A source array transfers across an actual memory-preserving step
when its five descriptor words and scratch conditions are retained. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)

theorem Table.Ready.transfer {n : ℕ} {a : Table n} {s t : Store} (h : a.Ready s)
    (hm : t.val.memory=s.val.memory)
    (hkeep : ∀i∈([200,202,203,204,205]:List ℕ),t.val.tapes i=s.val.tapes i)
    (hz : BankArray.Scratch t.val) (h7 : Blank t.val 7) : a.Ready t := by
  exact ⟨hz,h7,BankArray.word_of_eq (hkeep 200 (by simp)) h.width,
    BankArray.word_of_eq (hkeep 202 (by simp)) h.basePositive,
    BankArray.word_of_eq (hkeep 203 (by simp)) h.baseNegative,
    BankArray.word_of_eq (hkeep 204 (by simp)) h.baseDenominator,
    BankArray.word_of_eq (hkeep 205 (by simp)) h.clock,
    by simpa only [hm] using h.positive,by simpa only [hm] using h.negative,
    by simpa only [hm] using h.denominator⟩

#print axioms Table.Ready.transfer
end Maxwell.Continuum.RationalDataflow.PartArray
