import Maxwell.Continuum.RationalDataflowRowRead
import Maxwell.Continuum.RationalDataflowArrayOutputFrame

/-! Output-table metadata survives row-index preparation and cached reads. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem RowIndex.outputReady_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.OutputReady s) (f : BinaryPrecision.Frame RowIndex.changed s.val t.val)
    (hz : NatAssign.Scratch t.val) : a.OutputReady t := by
  refine ⟨⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),?_,?_,?_,?_⟩,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact RationalAccumulator.blank_of_eq (f.tapes 5 (by decide)) h.scratch.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (f.tapes 6 (by decide)) h.scratch.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (f.tapes 8 (by decide)) h.scratch.2.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (f.tapes 9 (by decide)) h.scratch.2.2.2.2.2.2.2
  · exact RationalAccumulator.blank_of_eq (f.tapes 7 (by decide)) h.seven
  · exact RationalAccumulator.blank_of_eq (f.tapes 37 (by decide)) h.packing
  · exact BankArray.word_of_eq (f.tapes 210 (by decide)) h.width
  · exact BankArray.word_of_eq (f.tapes 212 (by decide)) h.basePositive
  · exact BankArray.word_of_eq (f.tapes 213 (by decide)) h.baseNegative
  · exact BankArray.word_of_eq (f.tapes 214 (by decide)) h.baseDenominator
  · exact BankArray.word_of_eq (f.tapes 215 (by decide)) h.clock
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

theorem Table.OutputReady.rowRead_frame {n target : ℕ} {a : Table n} {s t : Store}
    (h : a.OutputReady s) (f : RowFrame target s.val t.val)
    (hz : BankArray.Scratch t.val) (h7 : RationalAccumulator.Blank t.val 7) : a.OutputReady t := by
  have keep (j : ℕ) (hj : 10 ≤ j) (hj' : j<1000) (hw : j∉RowIndex.ids) :=
    f.tapes j hj (by
      have hp := positivePort_ge target
      have hn := negativePort_ge target
      have hd := denominatorPort_ge target
      simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton,not_or]
      omega) hw
  refine ⟨hz,h7,RationalAccumulator.blank_of_eq (keep 37 (by decide) (by decide) (by decide)) h.packing,
    BankArray.word_of_eq (keep 210 (by decide) (by decide) (by decide)) h.width,
    BankArray.word_of_eq (keep 212 (by decide) (by decide) (by decide)) h.basePositive,
    BankArray.word_of_eq (keep 213 (by decide) (by decide) (by decide)) h.baseNegative,
    BankArray.word_of_eq (keep 214 (by decide) (by decide) (by decide)) h.baseDenominator,
    BankArray.word_of_eq (keep 215 (by decide) (by decide) (by decide)) h.clock,?_,?_,?_⟩
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

#print axioms Table.OutputReady.rowRead_frame
end Maxwell.Continuum.RationalDataflow.PartArray
