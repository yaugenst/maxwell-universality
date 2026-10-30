import Maxwell.Continuum.RationalDataflowArrayOutputFrame

/-! Metadata and array contents transfer through a framed runtime stage. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured

def tablePorts : Finset ℕ := {5,6,7,8,9,200,202,203,204,205}

theorem table_metadata_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.Ready s)
    (changed : Finset ℕ) (f : BinaryPrecision.Frame changed s.val t.val)
    (hd : Disjoint tablePorts changed) (hz : NatAssign.Scratch t.val) : a.Ready t := by
  have keep (i : ℕ) (hi : i∈tablePorts) : t.val.tapes i=s.val.tapes i :=
    f.tapes i (fun hh=>Finset.disjoint_left.mp hd hi hh)
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
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

#print axioms table_metadata_frame
end Maxwell.Continuum.RationalDataflow.PartArray
