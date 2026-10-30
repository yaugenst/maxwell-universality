import Maxwell.Continuum.RationalDataflowArray
import Maxwell.Continuum.RationalDataflowCounted

/-! Array metadata survives ordinary shared arithmetic and countdown tests. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2000000

theorem outside_workspace (S : Finset ℕ) (i : ℕ)
    (hi : (4 ≤ i ∧ i<30) ∨ (107 ≤ i ∧ i<1000)) : i∉workspace S := by
  intro hm
  rcases Finset.mem_union.mp hm with hs | hid
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    omega
  · rcases Finset.mem_union.mp hid with hp | hw
    · obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hp
      simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hr
      have hp := positivePort_ge r
      have hn := negativePort_ge r
      have hd := denominatorPort_ge r
      omega
    · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hw
      omega

namespace PartArray

theorem Table.Ready.arithmetic_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.Ready s) (S : Finset ℕ) (f : BinaryPrecision.Frame (workspace S) s.val t.val)
    (hz : NatAssign.Scratch t.val) : a.Ready t := by
  have keep (i : ℕ) (hi : (4 ≤ i ∧ i<30) ∨ (107 ≤ i ∧ i<1000)) :
      t.val.tapes i=s.val.tapes i := f.tapes i (outside_workspace S i hi)
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

theorem Table.Ready.count_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.Ready s) (f : CountedShifted.Frame 201 s t) : a.Ready t := by
  have keep (i : ℕ) (hi : i≠201) : t.val.tapes i=s.val.tapes i := f.2.2.2.2.2.1 i hi
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact RationalAccumulator.blank_of_eq (keep 0 (by decide)) h.scratch.1
  · exact RationalAccumulator.blank_of_eq (keep 1 (by decide)) h.scratch.2.1
  · exact RationalAccumulator.blank_of_eq (keep 2 (by decide)) h.scratch.2.2.1
  · exact RationalAccumulator.blank_of_eq (keep 3 (by decide)) h.scratch.2.2.2.1
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
  · simpa only [f.2.2.1] using h.positive
  · simpa only [f.2.2.1] using h.negative
  · simpa only [f.2.2.1] using h.denominator

#print axioms Table.Ready.arithmetic_frame
#print axioms Table.Ready.count_frame

end PartArray
end Maxwell.Continuum.RationalDataflow
