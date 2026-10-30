import Maxwell.Continuum.CalibrationRootFrequencyTail

/-! Exact preservation of the shared arithmetic state by frequency decoding. -/
namespace Maxwell.Continuum.RationalDataflow.RootFrequency
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2500000

theorem ids_bounds (i : ℕ) (hi : i∈ids) : 220 ≤ i ∧ i≤344 := by
  simp only [ids,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.mem_Icc] at hi
  omega

theorem ids_outside_rational (S : Finset ℕ) (i : ℕ) (hi : i∈ids) :
    i∉RationalDataflow.workspace S := by
  have hb := ids_bounds i hi
  have hp := RootSample.small_not_ports S i (by omega)
  simp only [RationalDataflow.workspace,RationalDataflow.ids,workPorts,temporaryPorts,
    RationalMagnitude.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  exact not_or_intro (by omega) (not_or_intro hp (by omega))

theorem ids_outside_glue (i : ℕ) (hi : i∈ids) : i∉GlueMachine.Runtime.ids := by
  have hb := ids_bounds i hi
  simp only [GlueMachine.Runtime.ids,GlueMachine.ids,GlueMachine.extra,
    SelectedParameters.Compare.ids,RationalTaylor.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem ids_outside_phase (i : ℕ) (hi : i∈ids) : i∉PhaseMachine.Runtime.ids := by
  have hb := ids_bounds i hi
  simp only [PhaseMachine.Runtime.ids,PhaseMachine.Runtime.extras,PhaseMachine.allIds,
    PhaseMachine.ids,Machin.allIds,RationalArctan.ids,RationalTaylor.ids,RationalMagnitude.ids,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem rational_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : Ready S v s) (f : BinaryPrecision.Frame changed s.val t.val)
    (hz : ∀i,i<5 → Blank t.val i) : Ready S v t := by
  refine ⟨?_,fun i hi => hz i (by omega)⟩
  intro i hi
  have hge := ids_ge_ten S i hi
  have hout : i∉changed := by
    intro hm
    rcases Finset.mem_union.mp hm with hm|hm
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      omega
    · exact ids_outside_rational S i hm (Finset.mem_union_right _ hi)
  exact word_of_eq (f.tapes i hout) (h.1 i hi)

theorem glue_frame {s t : Store} (h : Glue.Clean s.val)
    (f : BinaryPrecision.Frame changed s.val t.val)
    (hz : ∀i,i<5 → Blank t.val i) : Glue.Clean t.val := by
  intro i hi
  by_cases hs : i<5
  · exact hz i hs
  have hg := Finset.mem_of_mem_erase hi
  have hout : i∉changed := by
    intro hm
    rcases Finset.mem_union.mp hm with hm|hm
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      omega
    · exact ids_outside_glue i hm hg
  exact blank_of_eq (f.tapes i hout) (h i hi)

theorem phase_frame {s t : Store} (h : Phase.Runtime.Clean s.val)
    (f : BinaryPrecision.Frame changed s.val t.val)
    (hz : ∀i,i<5 → Blank t.val i) : Phase.Runtime.Clean t.val := by
  intro i hi
  by_cases hs : i<5
  · exact hz i hs
  have hp := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
  have hout : i∉changed := by
    intro hm
    rcases Finset.mem_union.mp hm with hm|hm
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      omega
    · exact ids_outside_phase i hm hp
  exact blank_of_eq (f.tapes i hout) (h i hi)

theorem output_frame {T : ℕ} {a : PartArray.Table T} {s t : Store} (h : a.OutputReady s)
    (f : BinaryPrecision.Frame changed s.val t.val)
    (hz : ∀i,i<5 → Blank t.val i) : a.OutputReady t := by
  have keep (i : ℕ) (hi : i∈([5,6,7,8,9,37,210,212,213,214,215]:List ℕ)) :
      t.val.tapes i=s.val.tapes i := by
    apply f.tapes i
    simp only [changed,ids,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.mem_Icc]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  have z : BankArray.Scratch t.val := by
    rcases h.scratch with ⟨_,_,_,_,h5,h6,h8,h9⟩
    exact ⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
      blank_of_eq (keep 5 (by simp)) h5,blank_of_eq (keep 6 (by simp)) h6,
      blank_of_eq (keep 8 (by simp)) h8,blank_of_eq (keep 9 (by simp)) h9⟩
  apply h.transfer f.memory _ z (blank_of_eq (keep 7 (by simp)) h.seven)
  intro i hi
  apply keep i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  tauto

#print axioms rational_frame
end Maxwell.Continuum.RationalDataflow.RootFrequency
