import Maxwell.Continuum.CalibrationRootSampleMachine
import Maxwell.Continuum.PhaseRuntimeDataflowFrame

/-! Cleanup and external words when the fixed glue and phase machines share
their arithmetic scratch.  Neither caller requires fresh global memory. -/
namespace Maxwell.Continuum.RationalDataflow.RootSample
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2500000

theorem small_not_ports (S : Finset ℕ) (i : ℕ) (hi : i<1000) : i∉ports S := by
  intro h
  obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp h
  have hp := positivePort_ge r
  have hn := negativePort_ge r
  have hd := denominatorPort_ge r
  simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hr
  omega

theorem glue_parameter_outside (S : Finset ℕ) (i : ℕ) (hi : i=652 ∨ i=653) :
    i∉Glue.workspace S := by
  have hr := Phase.Runtime.parameter_outside S i hi
  have hg : i∉GlueMachine.Runtime.ids := by rcases hi with rfl|rfl <;> decide
  simp only [Glue.workspace,Glue.allIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  exact not_or_intro (by omega) (not_or_intro hr hg)

theorem phase_glue_precision_outside (S : Finset ℕ) : 640∉Phase.Runtime.workspace S := by
  have hr := Glue.precision_outside S
  have hp : 640∉PhaseMachine.Runtime.ids := by decide
  simp only [Phase.Runtime.workspace,Phase.Runtime.allIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  exact not_or_intro (by omega) (not_or_intro hr hp)

theorem phase_clean_glue {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : Phase.Runtime.Clean s.val)
    (f : BinaryPrecision.Frame (Glue.workspace S) s.val t.val)
    (hr : Ready S v t) (hg : Glue.Clean t.val) : Phase.Runtime.Clean t.val := by
  intro i hi
  have hphase := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
  have hsmall := Phase.Runtime.ids_small i hphase
  have hge := PhaseMachine.Runtime.ids_ge i hphase
  have hne : i≠640 := by
    simp only [PhaseMachine.Runtime.ids,PhaseMachine.Runtime.extras,PhaseMachine.allIds,
      PhaseMachine.ids,Machin.allIds,RationalArctan.ids,RationalTaylor.ids,RationalMagnitude.ids,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hphase
    omega
  by_cases hdata : i∈RationalDataflow.ids S
  · have w := hr.1 i hdata
    rw [dataValues_small v hsmall] at w
    exact (zero_word_iff_blank _ _).mp w
  by_cases hglue : i∈GlueMachine.Runtime.ids
  · exact hg i (Finset.mem_erase.mpr ⟨hne,hglue⟩)
  apply blank_of_eq (f.tapes i _) (h i hi)
  simp only [Glue.workspace,Glue.allIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  exact not_or_intro (by omega) (not_or_intro hdata hglue)

theorem glue_clean_phase {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : Glue.Clean s.val)
    (f : BinaryPrecision.Frame (Phase.Runtime.workspace S) s.val t.val)
    (hr : Ready S v t) (hp : Phase.Runtime.Clean t.val) : Glue.Clean t.val := by
  intro i hi
  have hglue := Finset.mem_of_mem_erase hi
  have hsmall := Glue.ids_small i hglue
  have hge := GlueMachine.Runtime.ids_ge i hglue
  have h652 : i≠652 ∧ i≠653 := by
    simp only [GlueMachine.Runtime.ids,GlueMachine.ids,GlueMachine.extra,
      SelectedParameters.Compare.ids,RationalTaylor.ids,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hglue
    omega
  by_cases hdata : i∈RationalDataflow.ids S
  · have w := hr.1 i hdata
    rw [dataValues_small v hsmall] at w
    exact (zero_word_iff_blank _ _).mp w
  by_cases hphase : i∈PhaseMachine.Runtime.ids
  · exact hp i (Finset.mem_erase.mpr ⟨h652.2,Finset.mem_erase.mpr ⟨h652.1,hphase⟩⟩)
  apply blank_of_eq (f.tapes i _) (h i hi)
  simp only [Phase.Runtime.workspace,Phase.Runtime.allIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  exact not_or_intro (by omega) (not_or_intro hdata hphase)

#print axioms phase_clean_glue
#print axioms glue_clean_phase
end Maxwell.Continuum.RationalDataflow.RootSample
