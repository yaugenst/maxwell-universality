import Maxwell.Continuum.RationalDataflowDenominatorPass
import Maxwell.Cost.WordReplace

/-! Counter save/restore and denominator-pass preservation for the table converter. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 2500000
set_option maxRecDepth 32768

theorem denominator_protects_saved_count : (denominatorCode 0 1).protectsTape 206=true := by decide

theorem denominator_keeps {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (hex : Executes input tape (denominatorCode 0 1) cost s t) (i : ℕ)
    (hi : i∈denominatorProtectedPorts) : t.val.tapes i=s.val.tapes i :=
  hex.protectsTape i (List.all_eq_true.mp denominator_protects_auxiliary i hi)

theorem sharedReady_denominator_frame {v w : ℕ→Parts} {input : List Bool} {tape : ℕ→Bool}
    {cost : ℕ} {s t : Store} (h : SharedConversion.Ready sharedSlots v s)
    (hex : Executes input tape (denominatorCode 0 1) cost s t)
    (hn : RationalDataflow.Ready sharedSlots w t) : SharedConversion.Ready sharedSlots w t := by
  constructor
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hn.1 i hi
    · have old := h.1 i (Finset.mem_union_right _ hi)
      rw [SharedConversion.work_values_zero v i hi] at old
      rw [SharedConversion.work_values_zero w i hi]
      apply RationalAccumulator.word_of_eq (denominator_keeps hex i _) old
      simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide
  · intro i hi
    by_cases hl : i<4
    · exact hn.2 i hl
    · have : i=4 := by omega
      subst i
      exact RationalAccumulator.blank_of_eq (denominator_keeps hex 4 (by decide)) (h.2 4 (by decide))

theorem Table.OutputReady.denominator_frame {n : ℕ} {a : Table n} {input : List Bool} {tape : ℕ→Bool}
    {cost : ℕ} {s t : Store} (h : a.OutputReady s)
    (hex : Executes input tape (denominatorCode 0 1) cost s t)
    (hz : BankArray.Scratch t.val) (h7 : Blank t.val 7) : a.OutputReady t := by
  apply h.transfer (hex.protectsMemory denominator_protects_memory) _ hz h7
  intro i hi
  apply denominator_keeps hex i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem sharedReady_copy_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store} {target : ℕ}
    (h : SharedConversion.Ready S v s) (ht : target=201 ∨ target=206)
    (f : WordReplace.Frame target s.val t.val) : SharedConversion.Ready S v t := by
  constructor
  · intro i hi
    have hne : i≠target := by
      intro he
      subst i
      have hout : target∉SharedConversion.changed S := by
        rcases ht with rfl | rfl <;> exact outside_shared_changed S _ (by decide)
      exact hout (Finset.mem_union_right _ hi)
    exact RationalAccumulator.word_of_eq (f.2.2.2.2.2.1 i hne) (h.1 i hi)
  · intro i hi
    apply RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 i _) (h.2 i hi)
    rcases ht with rfl | rfl <;> omega

theorem Table.Ready.copy_frame {n : ℕ} {a : Table n} {s t : Store} {target : ℕ}
    (h : a.Ready s) (ht : target=201 ∨ target=206)
    (f : WordReplace.Frame target s.val t.val) : a.Ready t := by
  have keep (i : ℕ) (hi : i≠201 ∧ i≠206) : t.val.tapes i=s.val.tapes i :=
    f.2.2.2.2.2.1 i (by rcases ht with rfl | rfl <;> tauto)
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

theorem Table.OutputReady.copy_frame {n : ℕ} {a : Table n} {s t : Store} {target : ℕ}
    (h : a.OutputReady s) (ht : target=201 ∨ target=206)
    (f : WordReplace.Frame target s.val t.val) (hz : BankArray.Scratch t.val) (h7 : Blank t.val 7) :
    a.OutputReady t := by
  apply h.transfer f.2.2.1 _ hz h7
  intro i hi
  apply f.2.2.2.2.2.1 i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases ht with rfl | rfl <;> omega

#print axioms sharedReady_denominator_frame
#print axioms Table.Ready.copy_frame
end Maxwell.Continuum.RationalDataflow.PartArray
