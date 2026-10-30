import Maxwell.Continuum.PhaseDataflowCost
import Maxwell.Continuum.RationalDataflowArrayFrame

/-! Phase calls compose with the shared register and indexed-array machine. -/
namespace Maxwell.Continuum.RationalDataflow.Phase
open Maxwell.Cost Maxwell.Cost.Structured RationalTaylor
set_option maxHeartbeats 1500000

theorem Clean.arithmetic_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : Clean s.val) (f : BinaryPrecision.Frame (RationalDataflow.workspace S) s.val t.val)
    (hr : RationalDataflow.Ready S v t) : Clean t.val := by
  intro i hi
  by_cases hs : i∈RationalDataflow.ids S
  · have hw := hr.1 i hs
    rw [dataValues_small v (PhaseMachine.allIds_small i hi)] at hw
    exact (RationalAccumulator.zero_word_iff_blank _ _).mp hw
  · have hg := PhaseMachine.allIds_ge i hi
    have ho : i∉RationalDataflow.workspace S := by
      simp only [RationalDataflow.workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      exact not_or_intro (by omega) hs
    exact RationalAccumulator.blank_of_eq (f.tapes i ho) (h i hi)

theorem outside_workspace (S : Finset ℕ) (i : ℕ)
    (hi : (4 ≤ i ∧ i<30) ∨ (144 ≤ i ∧ i<220)) : i∉workspace S := by
  have hr : i∉RationalDataflow.workspace S := RationalDataflow.outside_workspace S i (by omega)
  have hp : i∉PhaseMachine.allIds := by
    simp only [PhaseMachine.allIds,PhaseMachine.ids,Machin.allIds,RationalArctan.ids,
      RationalMagnitude.ids,RationalTaylor.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega
  simp only [workspace,allIds,RationalDataflow.workspace,Finset.mem_union] at *
  tauto

theorem array_ready {n : ℕ} {a : PartArray.Table n} {s t : Store} (h : a.Ready s)
    (S : Finset ℕ) (f : BinaryPrecision.Frame (workspace S) s.val t.val)
    (hz : NatAssign.Scratch t.val) : a.Ready t := by
  have keep (i : ℕ) (hi : (4 ≤ i ∧ i<30) ∨ (144 ≤ i ∧ i<220)) :
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

#print axioms Clean.arithmetic_frame
#print axioms array_ready
end Maxwell.Continuum.RationalDataflow.Phase
