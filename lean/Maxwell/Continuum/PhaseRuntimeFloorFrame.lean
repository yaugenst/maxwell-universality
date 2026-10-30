import Maxwell.Continuum.PhaseRuntimeDataflowFrame
import Maxwell.Continuum.DyadicFloorFrame

/-! The fixed runtime phase workspace and exact integer-floor workspace
compose while preserving their actual cleanup and stored parameters. -/
namespace Maxwell.Continuum.RationalDataflow.DyadicFloor
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2500000

theorem high_outside_workspace (S : Finset ℕ) (i : ℕ) (hi : 600 ≤ i ∧ i<1000) :
    i∉workspace S := by
  have hr : i∉RationalDataflow.workspace S := RationalDataflow.outside_workspace S i (by omega)
  have hx : i∉extraIds∪NaturalQuotient.workPorts := by
    simp only [extraIds,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega
  have h4 : i≠4 := by omega
  simp only [workspace,allIds,RationalDataflow.workspace,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton] at *
  tauto

theorem Clean.runtimePhase_frame {S : Finset ℕ} {s t : Store} (h : Clean s.val)
    (f : BinaryPrecision.Frame (Phase.Runtime.workspace S) s.val t.val) : Clean t.val := by
  have outside (i : ℕ) (hi : i=4 ∨ i∈extraIds∪NaturalQuotient.workPorts) :
      i∉Phase.Runtime.workspace S := by
    have hsmall : i=4 ∨ (107 ≤ i ∧ i<600) := by
      simp only [extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    have hr := RationalDataflow.outside_workspace S i (by omega)
    have hp : i∉PhaseMachine.Runtime.ids := by
      simp only [PhaseMachine.Runtime.ids,PhaseMachine.Runtime.extras,PhaseMachine.allIds,
        PhaseMachine.ids,Machin.allIds,RationalArctan.ids,RationalMagnitude.ids,RationalTaylor.ids,
        Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      omega
    simp only [Phase.Runtime.workspace,Phase.Runtime.allIds,RationalDataflow.workspace,
      Finset.mem_union] at *
    tauto
  exact ⟨blank_of_eq (f.tapes 4 (outside 4 (Or.inl rfl))) h.1,
    fun i hi => blank_of_eq (f.tapes i (outside i (Or.inr hi))) (h.2 i hi)⟩

theorem runtimePhase_clean {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : Phase.Runtime.Clean s.val) (f : BinaryPrecision.Frame (workspace S) s.val t.val)
    (hr : Ready S v t) : Phase.Runtime.Clean t.val := by
  intro i hi
  have hp : i∈PhaseMachine.Runtime.ids := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
  by_cases hr' : i∈ids S
  · have hw := hr.1 i hr'
    rw [dataValues_small v (Phase.Runtime.ids_small i hp)] at hw
    exact (zero_word_iff_blank _ _).mp hw
  · have hg := PhaseMachine.Runtime.ids_ge i hp
    have hextra : i∉extraIds∪NaturalQuotient.workPorts := by
      simp only [PhaseMachine.Runtime.ids,PhaseMachine.Runtime.extras,PhaseMachine.allIds,
        PhaseMachine.ids,Machin.allIds,RationalArctan.ids,RationalMagnitude.ids,RationalTaylor.ids,
        Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hp
      simp only [extraIds,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      omega
    have h4 : i≠4 := by
      intro he
      subst i
      exact (by decide : 4∉PhaseMachine.Runtime.ids) hp
    have hout : i∉workspace S := by
      simp only [workspace,allIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hextra ⊢
      have hsmall : ¬(i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4) := by omega
      tauto
    exact blank_of_eq (f.tapes i hout) (h i hi)

#print axioms Clean.runtimePhase_frame
#print axioms runtimePhase_clean
end Maxwell.Continuum.RationalDataflow.DyadicFloor
