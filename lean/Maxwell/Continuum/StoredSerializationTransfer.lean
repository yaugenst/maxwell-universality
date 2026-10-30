import Maxwell.Continuum.StoredSerializationFrame

/-! Stored arrays survive output-producing routines when their memory and
metadata tapes are unchanged; emitted bits need not be framed. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured

theorem Table.Ready.memory_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.Ready s)
    (hm : t.val.memory=s.val.memory)
    (keep : ∀i∈tablePorts,t.val.tapes i=s.val.tapes i)
    (hz : NatAssign.Scratch t.val) : a.Ready t := by
  refine ⟨⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),?_,?_,?_,?_⟩,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact RationalAccumulator.blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2
  · exact RationalAccumulator.blank_of_eq (keep 7 (by decide)) h.seven
  · exact BankArray.word_of_eq (keep 200 (by decide)) h.width
  · exact BankArray.word_of_eq (keep 202 (by decide)) h.basePositive
  · exact BankArray.word_of_eq (keep 203 (by decide)) h.baseNegative
  · exact BankArray.word_of_eq (keep 204 (by decide)) h.baseDenominator
  · exact BankArray.word_of_eq (keep 205 (by decide)) h.clock
  · simpa only [hm] using h.positive
  · simpa only [hm] using h.negative
  · simpa only [hm] using h.denominator

#print axioms Table.Ready.memory_frame
end Maxwell.Continuum.RationalDataflow.PartArray
