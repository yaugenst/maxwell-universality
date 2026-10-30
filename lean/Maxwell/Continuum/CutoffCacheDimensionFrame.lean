import Maxwell.Continuum.CutoffCacheRuntimePrepare

/-! The fixed natural metadata preparation preserves both live tables and
the rational data bank, including their unrestricted memory contents. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

theorem cacheDimensions_rational_frame {v : ℕ→Parts} {s t : Store}
    (h : RationalDataflow.Ready (Finset.range 8) v s)
    (f : BinaryPrecision.Frame ({0,1,2,3}∪cacheDimensionIds) s.val t.val)
    (z : NatAssign.Scratch t.val) : RationalDataflow.Ready (Finset.range 8) v t := by
  refine ⟨?_,z⟩
  have hd : Disjoint (ids (Finset.range 8)) ({0,1,2,3}∪cacheDimensionIds) := by decide
  intro i hi
  exact RationalAccumulator.word_of_eq (f.tapes i (fun hh=>Finset.disjoint_left.mp hd hi hh)) (h.1 i hi)

theorem cacheDimensions_table_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.Ready s) (f : BinaryPrecision.Frame ({0,1,2,3}∪cacheDimensionIds) s.val t.val)
    (z : NatAssign.Scratch t.val) : a.Ready t := by
  refine ⟨⟨z 0 (by decide),z 1 (by decide),z 2 (by decide),z 3 (by decide),?_,?_,?_,?_⟩,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact RationalAccumulator.blank_of_eq (f.tapes 5 (by decide)) h.scratch.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (f.tapes 6 (by decide)) h.scratch.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (f.tapes 8 (by decide)) h.scratch.2.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (f.tapes 9 (by decide)) h.scratch.2.2.2.2.2.2.2
  · exact RationalAccumulator.blank_of_eq (f.tapes 7 (by decide)) h.seven
  · exact BankArray.word_of_eq (f.tapes 200 (by decide)) h.width
  · exact BankArray.word_of_eq (f.tapes 202 (by decide)) h.basePositive
  · exact BankArray.word_of_eq (f.tapes 203 (by decide)) h.baseNegative
  · exact BankArray.word_of_eq (f.tapes 204 (by decide)) h.baseDenominator
  · exact BankArray.word_of_eq (f.tapes 205 (by decide)) h.clock
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

theorem cacheDimensions_output_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.OutputReady s) (f : BinaryPrecision.Frame ({0,1,2,3}∪cacheDimensionIds) s.val t.val)
    (hz : BankArray.Scratch t.val) (h7 : RationalAccumulator.Blank t.val 7) : a.OutputReady t := by
  apply h.transfer f.memory _ hz h7
  intro i hi
  apply f.tapes i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

#print axioms cacheDimensions_table_frame
end Maxwell.Continuum.Calibration.RawCutoff
