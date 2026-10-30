import Maxwell.Continuum.ChebyshevWaveCacheData
import Maxwell.Continuum.RationalDataflowRowWritePlan
import Maxwell.Cost.Structured.Footprint

/-! Actual input/output table and runtime workspace preservation for wave
cache production and its two indexed writes. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def cachePreservedPorts : Finset ℕ := {5,6,7,8,9,37,200,201,202,203,204,205,210,212,213,214,215,681}
theorem cachePreservedPorts_disjoint : Disjoint cachePreservedPorts encodedWorkspace := by decide
theorem cache_preserved (i : ℕ) (hi : i∈cachePreservedPorts) : i∉encodedWorkspace :=
  Finset.disjoint_left.mp cachePreservedPorts_disjoint hi

theorem Table.Ready.wave_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.Ready s) (f : BinaryPrecision.Frame encodedWorkspace s.val t.val)
    (hz : NatAssign.Scratch t.val) : a.Ready t := by
  have keep (i : ℕ) (hi : i∈cachePreservedPorts) := f.tapes i (cache_preserved i hi)
  refine ⟨⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),?_,?_,?_,?_⟩,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1
  · exact blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1
  · exact blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1
  · exact blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2
  · exact blank_of_eq (keep 7 (by decide)) h.seven
  · exact BankArray.word_of_eq (keep 200 (by decide)) h.width
  · exact BankArray.word_of_eq (keep 202 (by decide)) h.basePositive
  · exact BankArray.word_of_eq (keep 203 (by decide)) h.baseNegative
  · exact BankArray.word_of_eq (keep 204 (by decide)) h.baseDenominator
  · exact BankArray.word_of_eq (keep 205 (by decide)) h.clock
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

theorem Table.OutputReady.wave_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.OutputReady s) (f : BinaryPrecision.Frame encodedWorkspace s.val t.val)
    (hz : NatAssign.Scratch t.val) : a.OutputReady t := by
  have keep (i : ℕ) (hi : i∈cachePreservedPorts) := f.tapes i (cache_preserved i hi)
  refine ⟨⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),?_,?_,?_,?_⟩,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1
  · exact blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1
  · exact blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1
  · exact blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2
  · exact blank_of_eq (keep 7 (by decide)) h.seven
  · exact blank_of_eq (keep 37 (by decide)) h.packing
  · exact BankArray.word_of_eq (keep 210 (by decide)) h.width
  · exact BankArray.word_of_eq (keep 212 (by decide)) h.basePositive
  · exact BankArray.word_of_eq (keep 213 (by decide)) h.baseNegative
  · exact BankArray.word_of_eq (keep 214 (by decide)) h.baseDenominator
  · exact BankArray.word_of_eq (keep 215 (by decide)) h.clock
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

def cacheWritePlan : List (ℕ×ℕ) := [(0,8),(1,9)]
def cacheWriteCode : Code := rowWritePlanCode 2 cacheWritePlan
theorem cacheWrite_protects_four : cacheWriteCode.protectsTape 4=true := by decide

theorem LoopReady.rowWrite_frame {Q P : ℕ} {v : ℕ→Parts} {s t : Store}
    (h : LoopReady Q P v s) (f : RowWriteFrame s.val t.val) (hr : Ready ids v t)
    (h4 : t.val.tapes 4=s.val.tapes 4) (hz : ∀i∈RowIndex.ids,Blank t.val i) :
    LoopReady Q P v t := by
  have keep (i : ℕ) (hi : 10 ≤ i) (h37 : i≠37) (hid : i∉RowIndex.ids) := f.tapes i hi h37 hid
  refine ⟨hr,?_,⟨blank_of_eq h4 h.floor.1,?_⟩,?_,
    word_of_eq (keep 652 (by decide) (by decide) (by decide)) h.rangeWord,
    word_of_eq (keep 653 (by decide) (by decide) (by decide)) h.precisionWord⟩
  · intro i hi
    have hip : i∈PhaseMachine.Runtime.ids := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hd : ∀i∈PhaseMachine.Runtime.ids,10 ≤ i ∧ i≠37 ∧ i∉RowIndex.ids := by decide
    have hd' := hd i hip
    exact blank_of_eq (keep i hd'.1 hd'.2.1 hd'.2.2) (h.phase i hi)
  · intro i hi
    by_cases hid : i∈RowIndex.ids
    · exact hz i hid
    · have hh : 10 ≤ i ∧ i≠37 := by
        simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton] at hi
        omega
      exact blank_of_eq (keep i hh.1 hh.2 hid) (h.floor.2 i hi)
  · intro i hi
    have hp := parameterIds_range i hi
    have hn : i∉RowIndex.ids := by
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact word_of_eq (keep i (by omega) (by omega) hn) (h.parameters i hi)

theorem LoopReady.count201_frame {Q P : ℕ} {v : ℕ→Parts} {s t : Store}
    (h : LoopReady Q P v s) (f : CountedShifted.Frame 201 s t) : LoopReady Q P v t := by
  have keep (i : ℕ) (hi : i≠201) := f.2.2.2.2.2.1 i hi
  refine ⟨RationalDataflow.Ready.count_frame ids v 201
    (RationalDataflow.outside_workspace ids 201 (by decide)) h.ready f,?_,⟨?_,?_⟩,?_,
    word_of_eq (keep 652 (by decide)) h.rangeWord,word_of_eq (keep 653 (by decide)) h.precisionWord⟩
  · intro i hi
    have hip : i∈PhaseMachine.Runtime.ids := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hn : i≠201 := by intro he;subst i;exact (by decide : 201∉PhaseMachine.Runtime.ids) hip
    exact blank_of_eq (keep i hn) (h.phase i hi)
  · exact blank_of_eq (keep 4 (by decide)) h.floor.1
  · intro i hi
    have hn : i≠201 := by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact blank_of_eq (keep i hn) (h.floor.2 i hi)
  · intro i hi
    have hh := parameterIds_range i hi
    exact word_of_eq (keep i (by omega)) (h.parameters i hi)

#print axioms Table.Ready.wave_frame
#print axioms LoopReady.rowWrite_frame
end Maxwell.Continuum.Profile.WaveMachine.Runtime
