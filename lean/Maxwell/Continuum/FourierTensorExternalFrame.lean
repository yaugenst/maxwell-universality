import Maxwell.Continuum.FourierTensorEmitFrame

/-! The tensor traversal counters lie above every represented rational,
phase, Fourier, and wave-cache tape. Their actual effects preserve those
banks without an assumed machine invariant. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator

theorem Ready.low_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store} {K : ℕ}
    (h : Ready S v s) (hK : 4 ≤ K) (hids : ∀i∈ids S,i<K)
    (ht : ∀i,i<K → t.val.tapes i=s.val.tapes i) : Ready S v t :=
  ⟨fun i hi => word_of_eq (ht i (hids i hi)) (h.1 i hi),
    fun i hi => blank_of_eq (ht i (hi.trans_le hK)) (h.2 i hi)⟩

namespace PartArray
theorem Table.Ready.low_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.Ready s) (hm : t.val.memory=s.val.memory)
    (ht : ∀i,i<206 → t.val.tapes i=s.val.tapes i) : a.Ready t := by
  have hz : BankArray.Scratch t.val := by
    rcases h.scratch with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨blank_of_eq (ht 0 (by decide)) h0,blank_of_eq (ht 1 (by decide)) h1,
      blank_of_eq (ht 2 (by decide)) h2,blank_of_eq (ht 3 (by decide)) h3,
      blank_of_eq (ht 5 (by decide)) h5,blank_of_eq (ht 6 (by decide)) h6,
      blank_of_eq (ht 8 (by decide)) h8,blank_of_eq (ht 9 (by decide)) h9⟩
  exact ⟨hz,blank_of_eq (ht 7 (by decide)) h.seven,
    BankArray.word_of_eq (ht 200 (by decide)) h.width,
    BankArray.word_of_eq (ht 202 (by decide)) h.basePositive,
    BankArray.word_of_eq (ht 203 (by decide)) h.baseNegative,
    BankArray.word_of_eq (ht 204 (by decide)) h.baseDenominator,
    BankArray.word_of_eq (ht 205 (by decide)) h.clock,
    by simpa only [hm] using h.positive,
    by simpa only [hm] using h.negative,
    by simpa only [hm] using h.denominator⟩
end PartArray
end Maxwell.Continuum.RationalDataflow

namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
set_option maxHeartbeats 2500000
set_option maxRecDepth 32768

theorem FactorReady.low_frame {n D Q N : ℕ} {a : Table n} {b : Table (2*D)}
    {v : ℕ→Parts} {s t : Store} (h : FactorReady a Q N b v s)
    (hm : t.val.memory=s.val.memory) (ht : ∀i,i<1099 → t.val.tapes i=s.val.tapes i) :
    FactorReady a Q N b v t := by
  have source := h.source.low_frame hm (fun i hi => ht i (by omega))
  refine ⟨h.ready.low_frame (by decide) (by decide) ht,?_,?_,?_,source,?_,
    blank_of_eq (ht 144 (by decide)) h.power,blank_of_eq (ht 146 (by decide)) h.powerCount,
    blank_of_eq (ht 680 (by decide)) h.inner,?_⟩
  · intro i hi
    have hb : ∀i∈(PhaseMachine.Runtime.ids.erase 652).erase 653,i<1099 := by decide
    exact blank_of_eq (ht i (hb i hi)) (h.phase i hi)
  · refine ⟨blank_of_eq (ht 4 (by decide)) h.floor.1,?_⟩
    intro i hi
    have hb : ∀i∈DyadicFloor.extraIds∪NaturalQuotient.workPorts,i<1099 := by decide
    exact blank_of_eq (ht i (hb i hi)) (h.floor.2 i hi)
  · intro i hi
    have hb : ∀i∈setupIds,i<1099 := by decide
    exact word_of_eq (ht i (hb i hi)) (h.setup i hi)
  · apply h.output.transfer hm _ source.scratch source.seven
    intro i hi
    exact ht i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega)
  · intro i hi
    exact blank_of_eq (ht i ((savedPorts_range i hi).2.trans_lt (by decide))) (h.saved i hi)

theorem termReady_external {v : ℕ→Parts} {s t : Store} (h : Ready termBank v s)
    (ht : ∀i,i<1099 → t.val.tapes i=s.val.tapes i) : Ready termBank v t :=
  h.low_frame (by decide) (by decide) ht

end Maxwell.Continuum.Profile.WaveMachine.Runtime
