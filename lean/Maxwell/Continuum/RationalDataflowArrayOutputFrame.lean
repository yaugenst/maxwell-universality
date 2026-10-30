import Maxwell.Continuum.RationalDataflowArrayOutput
import Maxwell.Continuum.RationalDataflowArrayFrame
import Maxwell.Continuum.RationalDataflowReadFootprint

/-! Frames for the read, convert, and indexed-write traversal. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem outside_shared_changed (S : Finset ℕ) (i : ℕ)
    (hi : 5 ≤ i ∧ i<1000 ∧ i∉workPorts ∧ i∉NaturalQuotient.workPorts) :
    i∉SharedConversion.changed S := by
  intro hh
  rcases Finset.mem_union.mp hh with hh | hh
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    omega
  · rcases Finset.mem_union.mp hh with hh | hh
    · rcases Finset.mem_union.mp hh with hh | hh
      · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hh
        have hp := positivePort_ge j
        have hn := negativePort_ge j
        have hd := denominatorPort_ge j
        simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hj
        omega
      · exact hi.2.2.1 hh
    · exact hi.2.2.2 hh

namespace PartArray

theorem sharedReady_read_frame {S : Finset ℕ} {v w : ℕ→Parts} {s t : Store}
    (h : SharedConversion.Ready S v s) (f : Frame 1 s.val t.val)
    (h4 : t.val.tapes 4=s.val.tapes 4) (hb : RationalDataflow.Ready S w t) :
    SharedConversion.Ready S w t := by
  constructor
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hb.1 i hi
    · have hig : 10 ≤ i := by simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi; omega
      have hil : i<1000 := by simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi; omega
      have hn : i∉cellPorts 1 := by simp [cellPorts,positivePort,negativePort,denominatorPort]; omega
      have old := h.1 i (Finset.mem_union_right _ hi)
      rw [SharedConversion.work_values_zero v i hi] at old
      rw [SharedConversion.work_values_zero w i hi]
      exact RationalAccumulator.word_of_eq (f.tapes i hig hn) old
  · intro i hi
    by_cases hlt : i<4
    · exact hb.2 i hlt
    · have : i=4 := by omega
      subst i
      exact RationalAccumulator.blank_of_eq h4 (h.2 4 (by decide))

theorem sharedReady_count_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : SharedConversion.Ready S v s) (f : CountedShifted.Frame 201 s t) :
    SharedConversion.Ready S v t := by
  constructor
  · intro i hi
    have hn : i≠201 := by
      intro he
      subst i
      exact outside_shared_changed S 201 (by decide) (Finset.mem_union_right _ hi)
    exact RationalAccumulator.word_of_eq (f.2.2.2.2.2.1 i hn) (h.1 i hi)
  · intro i hi
    exact RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 i (by omega)) (h.2 i hi)

theorem Table.Ready.shared_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.Ready s)
    (S : Finset ℕ) (f : BinaryPrecision.Frame (SharedConversion.changed S) s.val t.val)
    (hz : ∀ i, i<5 → Blank t.val i) : a.Ready t := by
  have keep (i : ℕ) (hi : 5 ≤ i ∧ i<1000 ∧ i∉workPorts ∧ i∉NaturalQuotient.workPorts) :=
    f.tapes i (outside_shared_changed S i hi)
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

theorem Table.OutputReady.transfer {n : ℕ} {a : Table n} {s t : Store} (h : a.OutputReady s)
    (hm : t.val.memory=s.val.memory)
    (hkeep : ∀ i∈([37,210,212,213,214,215]:List ℕ), t.val.tapes i=s.val.tapes i)
    (hz : BankArray.Scratch t.val) (h7 : Blank t.val 7) : a.OutputReady t := by
  exact ⟨hz,h7,RationalAccumulator.blank_of_eq (hkeep 37 (by simp)) h.packing,
    BankArray.word_of_eq (hkeep 210 (by simp)) h.width,
    BankArray.word_of_eq (hkeep 212 (by simp)) h.basePositive,
    BankArray.word_of_eq (hkeep 213 (by simp)) h.baseNegative,
    BankArray.word_of_eq (hkeep 214 (by simp)) h.baseDenominator,
    BankArray.word_of_eq (hkeep 215 (by simp)) h.clock,
    by simpa only [hm] using h.positive,by simpa only [hm] using h.negative,
    by simpa only [hm] using h.denominator⟩

theorem Table.OutputReady.read_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.OutputReady s)
    (f : Frame 1 s.val t.val) (hz : BankArray.Scratch t.val) (h7 : Blank t.val 7) : a.OutputReady t := by
  apply h.transfer f.memory _ hz h7
  intro i hi
  have hil : i<1000 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; omega
  apply f.tapes i
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  · simp [cellPorts,positivePort,negativePort,denominatorPort]
    omega

theorem Table.OutputReady.shared_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.OutputReady s)
    (S : Finset ℕ) (f : BinaryPrecision.Frame (SharedConversion.changed S) s.val t.val)
    (hz : BankArray.Scratch t.val) (h7 : Blank t.val 7) : a.OutputReady t := by
  apply h.transfer f.memory _ hz h7
  intro i hi
  apply f.tapes i (outside_shared_changed S i _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem Table.OutputReady.count_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.OutputReady s)
    (f : CountedShifted.Frame 201 s t) : a.OutputReady t := by
  have keep (i : ℕ) (hi : i≠201) := f.2.2.2.2.2.1 i hi
  have hz : BankArray.Scratch t.val := by
    rcases h.scratch with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (keep 0 (by decide)) h0,
      RationalAccumulator.blank_of_eq (keep 1 (by decide)) h1,
      RationalAccumulator.blank_of_eq (keep 2 (by decide)) h2,
      RationalAccumulator.blank_of_eq (keep 3 (by decide)) h3,
      RationalAccumulator.blank_of_eq (keep 5 (by decide)) h5,
      RationalAccumulator.blank_of_eq (keep 6 (by decide)) h6,
      RationalAccumulator.blank_of_eq (keep 8 (by decide)) h8,
      RationalAccumulator.blank_of_eq (keep 9 (by decide)) h9⟩
  apply h.transfer f.2.2.1 _ hz (RationalAccumulator.blank_of_eq (keep 7 (by decide)) h.seven)
  intro i hi
  apply keep i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

def Table.SeparatedFrom {n m : ℕ} (a : Table n) (b : Table m) : Prop :=
  ∀ x∈[a.basePositive,a.baseNegative,a.baseDenominator],
  ∀ y∈[b.basePositive,b.baseNegative,b.baseDenominator],
    IncidenceEncoding.Separated (addressValue x) (n*addressValue a.width)
      (addressValue y) (m*addressValue b.width)

theorem Table.writeMemory_preserves {n m : ℕ} (b : Table m) (i : Fin m) (x : Parts)
    {memory : ℕ→Bool} {base width : ℕ} {words : Vector (List Bool) n}
    (h : BitArray.Represents memory base width words)
    (hsep : ∀ y∈[b.basePositive,b.baseNegative,b.baseDenominator],
      IncidenceEncoding.Separated base (n*width) (addressValue y) (m*addressValue b.width)) :
    BitArray.Represents (b.writeMemory i x memory) base width words := by
  apply IncidenceEncoding.represents_write_disjoint _ _ _ i _ (FixedWidth.bits_length _ _) (hsep _ (by simp))
  apply IncidenceEncoding.represents_write_disjoint _ _ _ i _ (FixedWidth.bits_length _ _) (hsep _ (by simp))
  exact IncidenceEncoding.represents_write_disjoint h _ _ i _ (FixedWidth.bits_length _ _) (hsep _ (by simp))

theorem Table.Ready.write_output_frame {n m : ℕ} {a : Table n} {b : Table m} {s t : Store}
    (h : a.Ready s) (hsep : a.SeparatedFrom b) (i : Fin m) (x : Parts)
    (hm : t.val.memory=b.writeMemory i x s.val.memory) (f : BankArray.FrameExcept 37 s.val t.val)
    (hz : BankArray.Scratch t.val) (h7 : Blank t.val 7) : a.Ready t := by
  have keep (j : ℕ) (hj : 100 ≤ j) := f.2.2.2.1 j (Or.inr (by omega)) (by omega)
  refine ⟨hz,h7,BankArray.word_of_eq (keep _ (by decide)) h.width,
    BankArray.word_of_eq (keep _ (by decide)) h.basePositive,
    BankArray.word_of_eq (keep _ (by decide)) h.baseNegative,
    BankArray.word_of_eq (keep _ (by decide)) h.baseDenominator,
    BankArray.word_of_eq (keep _ (by decide)) h.clock,?_,?_,?_⟩
  · rw [hm]
    exact b.writeMemory_preserves i x h.positive (hsep _ (by simp))
  · rw [hm]
    exact b.writeMemory_preserves i x h.negative (hsep _ (by simp))
  · rw [hm]
    exact b.writeMemory_preserves i x h.denominator (hsep _ (by simp))

#print axioms Table.Ready.write_output_frame
#print axioms sharedReady_read_frame
end PartArray
end Maxwell.Continuum.RationalDataflow
