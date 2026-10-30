import Maxwell.Continuum.FourierTensorModeIndex
import Maxwell.Continuum.RationalDataflowArrayOutputFrame

/-! The concrete row-index workspace is separate from the stored Fourier
arrays, their descriptors, and the reusable rational register bank. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeIndex
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem changed_mem (i : ℕ) (hi : i∈changed) : i<4 ∨ 310 ≤ i ∧ i ≤ 322 := by
  simp only [changed,ports,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
  omega

theorem ready_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : RationalDataflow.Ready S v s) (f : BinaryPrecision.Frame changed s.val t.val)
    (hz : NatAssign.Scratch t.val) : RationalDataflow.Ready S v t := by
  refine ⟨?_,hz⟩
  intro i hi
  have hout : i∉changed := by
    intro hm
    have h := changed_mem i hm
    rcases h with h|h
    · have := ids_ge_ten S i hi;omega
    · exact outside_workspace S i (by omega) (Finset.mem_union_right _ hi)
  exact RationalAccumulator.word_of_eq (f.tapes i hout) (h.1 i hi)

theorem table_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.Ready s) (f : BinaryPrecision.Frame changed s.val t.val)
    (hz : NatAssign.Scratch t.val) : a.Ready t := by
  have keep (i : ℕ) (hi : 4 ≤ i) (hj : i<310) := f.tapes i (by
    intro hm;have hh := changed_mem i hm;omega)
  refine ⟨⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
    RationalAccumulator.blank_of_eq (keep 5 (by decide) (by decide)) h.scratch.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 6 (by decide) (by decide)) h.scratch.2.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 8 (by decide) (by decide)) h.scratch.2.2.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 9 (by decide) (by decide)) h.scratch.2.2.2.2.2.2.2⟩,
    RationalAccumulator.blank_of_eq (keep 7 (by decide) (by decide)) h.seven,
    BankArray.word_of_eq (keep 200 (by decide) (by decide)) h.width,
    BankArray.word_of_eq (keep 202 (by decide) (by decide)) h.basePositive,
    BankArray.word_of_eq (keep 203 (by decide) (by decide)) h.baseNegative,
    BankArray.word_of_eq (keep 204 (by decide) (by decide)) h.baseDenominator,
    BankArray.word_of_eq (keep 205 (by decide) (by decide)) h.clock,?_,?_,?_⟩
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

theorem output_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.OutputReady s) (f : BinaryPrecision.Frame changed s.val t.val)
    (hz : BankArray.Scratch t.val) (h7 : Blank t.val 7) : a.OutputReady t := by
  apply h.transfer f.memory _ hz h7
  intro i hi
  have hi' : i<310 ∧ 4 ≤ i := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  exact f.tapes i (by intro hm;have := changed_mem i hm;omega)

theorem floor_frame {s t : Store} (h : DyadicFloor.Clean s.val)
    (f : BinaryPrecision.Frame changed s.val t.val) : DyadicFloor.Clean t.val := by
  refine ⟨RationalAccumulator.blank_of_eq (f.tapes 4 (by decide)) h.1,?_⟩
  intro i hi
  have hout : i∉changed := by
    have hh : 4 ≤ i ∧ i<310 := by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    intro hm;have := changed_mem i hm;omega
  exact RationalAccumulator.blank_of_eq (f.tapes i hout) (h.2 i hi)

theorem read_tapes {target : ℕ} {s t : BitRAMState} (f : PartArray.Frame target s t)
    (i : ℕ) (hlo : 10 ≤ i) (hhi : i<1000) : t.tapes i=s.tapes i := by
  apply f.tapes i hlo
  have hp := positivePort_ge target
  have hn := negativePort_ge target
  have hd := denominatorPort_ge target
  simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem read_output_frame {n target : ℕ} {a : Table n} {s t : Store}
    (h : a.OutputReady s) (f : PartArray.Frame target s.val t.val)
    (hz : BankArray.Scratch t.val) (h7 : Blank t.val 7) : a.OutputReady t := by
  apply h.transfer f.memory _ hz h7
  intro i hi
  have hh : 10 ≤ i ∧ i<1000 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  exact read_tapes f i hh.1 hh.2

theorem read_floor_frame {target : ℕ} {s t : Store} (h : DyadicFloor.Clean s.val)
    (f : PartArray.Frame target s.val t.val) (h4 : t.val.tapes 4=s.val.tapes 4) :
    DyadicFloor.Clean t.val := by
  refine ⟨RationalAccumulator.blank_of_eq h4 h.1,?_⟩
  intro i hi
  have hh : 10 ≤ i ∧ i<1000 := by
    simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  exact RationalAccumulator.blank_of_eq (read_tapes f i hh.1 hh.2) (h.2 i hi)

#print axioms floor_frame
#print axioms read_output_frame
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeIndex
