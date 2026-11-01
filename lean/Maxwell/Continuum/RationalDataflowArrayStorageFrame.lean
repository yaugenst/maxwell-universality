import Maxwell.Continuum.RationalDataflowArrayFrame

/-! Array storage is retained whenever its memory and descriptor words agree. -/
namespace Maxwell.Continuum
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow RationalDataflow.PartArray

theorem RationalDataflow.PartArray.Table.Ready.storage_frame {n : ℕ} {a : Table n}
    {s t : Store} (h : a.Ready s) (memory : t.val.memory=s.val.memory)
    (keep : ∀i∈({200,202,203,204,205}:Finset ℕ),t.val.tapes i=s.val.tapes i)
    (scratch : BankArray.Scratch t.val) (seven : Blank t.val 7) : a.Ready t:=
  ⟨scratch,seven,BankArray.word_of_eq (keep 200 (by decide)) h.width,
    BankArray.word_of_eq (keep 202 (by decide)) h.basePositive,
    BankArray.word_of_eq (keep 203 (by decide)) h.baseNegative,
    BankArray.word_of_eq (keep 204 (by decide)) h.baseDenominator,
    BankArray.word_of_eq (keep 205 (by decide)) h.clock,
    by simpa only [memory] using h.positive,by simpa only [memory] using h.negative,
    by simpa only [memory] using h.denominator⟩

end Maxwell.Continuum
