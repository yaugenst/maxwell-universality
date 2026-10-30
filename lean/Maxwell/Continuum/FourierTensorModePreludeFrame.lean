import Maxwell.Continuum.FourierTensorModePrelude

/-! The normalization prelude retains the represented calibration array
and every allocated-input parameter required by the component compiler. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrelude
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768

theorem table_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.Ready s)
    (f : BinaryPrecision.Frame changed s.val t.val) (hz : NatAssign.Scratch t.val) : a.Ready t := by
  have keep (i : ℕ) (hi : i∈({5,6,7,8,9,200,202,203,204,205}:Finset ℕ)) :=
    f.tapes i (Finset.disjoint_left.mp (by decide : Disjoint
      ({5,6,7,8,9,200,202,203,204,205}:Finset ℕ) changed) hi)
  have scratch : BankArray.Scratch t.val :=
    ⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
     RationalAccumulator.blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2⟩
  apply h.transfer f.memory _ scratch (RationalAccumulator.blank_of_eq (keep 7 (by decide)) h.seven)
  intro i hi
  apply keep
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide

theorem output_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.OutputReady s)
    (f : BinaryPrecision.Frame changed s.val t.val)
    (hz : BankArray.Scratch t.val) (h7 : Blank t.val 7) : a.OutputReady t := by
  apply h.transfer f.memory _ hz h7
  intro i hi
  have hm : i∈({37,210,212,213,214,215}:Finset ℕ) := by simpa using hi
  exact f.tapes i (Finset.disjoint_left.mp
    (by decide : Disjoint ({37,210,212,213,214,215}:Finset ℕ) changed) hm)

theorem phase_frame {s t : Store} {v : ℕ→Parts} (h : Phase.Runtime.Clean s.val)
    (f : BinaryPrecision.Frame changed s.val t.val) (hr : Ready RowArithmetic.bank v t) :
    Phase.Runtime.Clean t.val := by
  intro i hi
  by_cases low : i∈RationalMagnitude.ids
  · have him : i∈RationalDataflow.ids RowArithmetic.bank :=
      Finset.mem_union_right _ (Finset.mem_union_right _ low)
    have hlow : i<1000 := by
      simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton] at low
      omega
    have word := hr.1 i him
    rw [dataValues_small v hlow,RationalAccumulator.zero_word_iff_blank] at word
    exact word
  · exact RationalAccumulator.blank_of_eq (f.tapes i (Finset.disjoint_left.mp
      (by decide : Disjoint (((PhaseMachine.Runtime.ids.erase 652).erase 653)\RationalMagnitude.ids) changed)
      (Finset.mem_sdiff.mpr ⟨hi,low⟩))) (h i hi)

theorem floor_frame {s t : Store} (h : DyadicFloor.Clean s.val)
    (f : BinaryPrecision.Frame changed s.val t.val) : DyadicFloor.Clean t.val := by
  refine ⟨RationalAccumulator.blank_of_eq (f.tapes 4 (by decide)) h.1,?_⟩
  intro i hi
  exact RationalAccumulator.blank_of_eq (f.tapes i (Finset.disjoint_left.mp
    (by decide : Disjoint (DyadicFloor.extraIds∪NaturalQuotient.workPorts) changed) hi)) (h.2 i hi)

theorem setup_frame {Q N : ℕ} {s t : Store}
    (h : NatAssign.Bank setupIds (initialSetup Q N) s.val)
    (f : BinaryPrecision.Frame changed s.val t.val) : NatAssign.Bank setupIds (initialSetup Q N) t.val := by
  intro i hi
  exact RationalAccumulator.word_of_eq (f.tapes i (Finset.disjoint_left.mp
    (by decide : Disjoint setupIds changed) hi)) (h i hi)

theorem fresh_frame {s t : Store} (h : ∀i∈TensorStart.freshPorts,Blank s.val i)
    (f : BinaryPrecision.Frame changed s.val t.val) : ∀i∈TensorStart.freshPorts,Blank t.val i := by
  intro i hi
  exact RationalAccumulator.blank_of_eq (f.tapes i (Finset.disjoint_left.mp
    (by decide : Disjoint TensorStart.freshPorts changed) hi)) (h i hi)

theorem allocation_frame {M L R P width bp bn bd : ℕ} {s t : Store}
    (h : NatAssign.Bank ModeAllocation.ids (ModeAllocation.initial M L R P width bp bn bd) s.val)
    (f : BinaryPrecision.Frame changed s.val t.val)
    (wm : Word t.val 350 M) (wl : Word t.val 352 L) (z353 : Blank t.val 353) :
    NatAssign.Bank ModeAllocation.ids (ModeAllocation.initial M L R P width bp bn bd) t.val := by
  intro i hi
  by_cases h350 : i=350
  · subst i;simpa [ModeAllocation.initial] using wm
  by_cases h352 : i=352
  · subst i;simpa [ModeAllocation.initial] using wl
  by_cases h353 : i=353
  · subst i;simpa [ModeAllocation.initial,RationalAccumulator.zero_word_iff_blank] using z353
  have he : i∈((ModeAllocation.ids.erase 350).erase 352).erase 353 := by
    simp only [Finset.mem_erase]
    exact ⟨h353,h352,h350,hi⟩
  exact RationalAccumulator.word_of_eq (f.tapes i (Finset.disjoint_left.mp
    (by decide : Disjoint (((ModeAllocation.ids.erase 350).erase 352).erase 353) changed) he)) (h i hi)

#print axioms allocation_frame
#print axioms fresh_frame
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrelude
