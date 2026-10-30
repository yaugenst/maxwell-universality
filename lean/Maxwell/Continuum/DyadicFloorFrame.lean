import Maxwell.Continuum.DyadicFloorCost
import Maxwell.Continuum.PhaseDataflowFrame

/-! Exact preservation of shared arrays and elementary-call scratch
between phase evaluation, arithmetic, and floor rounding. -/
namespace Maxwell.Continuum.RationalDataflow.DyadicFloor
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 1500000

theorem Clean.arithmetic_frame {S : Finset ℕ} {s t : Store} (h : Clean s.val)
    (f : BinaryPrecision.Frame (RationalDataflow.workspace S) s.val t.val) : Clean t.val := by
  refine ⟨RationalAccumulator.blank_of_eq (f.tapes 4 (RationalDataflow.outside_workspace S 4 (by decide))) h.1,?_⟩
  intro i hi
  have ho : i∉RationalDataflow.workspace S := by
    apply RationalDataflow.outside_workspace
    simp only [extraIds,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  exact RationalAccumulator.blank_of_eq (f.tapes i ho) (h.2 i hi)

theorem Clean.phase_frame {S : Finset ℕ} {s t : Store} (h : Clean s.val)
    (f : BinaryPrecision.Frame (Phase.workspace S) s.val t.val) : Clean t.val := by
  have outside (i : ℕ) (hi : i∈extraIds∪NaturalQuotient.workPorts) : i∉Phase.workspace S := by
    have hg : 107 ≤ i ∧ i<600 := by
      simp only [extraIds,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    have hr := RationalDataflow.outside_workspace S i (Or.inr ⟨hg.1,by omega⟩)
    have hp : i∉PhaseMachine.allIds := by
      simp only [PhaseMachine.allIds,PhaseMachine.ids,Machin.allIds,RationalArctan.ids,
        RationalMagnitude.ids,RationalTaylor.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      omega
    simp only [Phase.workspace,Phase.allIds,RationalDataflow.workspace,Finset.mem_union] at *
    tauto
  exact ⟨RationalAccumulator.blank_of_eq (f.tapes 4 (Phase.outside_workspace S 4 (by decide))) h.1,
    fun i hi => RationalAccumulator.blank_of_eq (f.tapes i (outside i hi)) (h.2 i hi)⟩

theorem phase_clean {S : Finset ℕ} {v : ℕ→Parts} {s t : Store} (h : Phase.Clean s.val)
    (f : BinaryPrecision.Frame (workspace S) s.val t.val) (hr : Ready S v t) : Phase.Clean t.val := by
  intro i hi
  by_cases hr' : i∈ids S
  · have hw := hr.1 i hr'
    rw [dataValues_small v (PhaseMachine.allIds_small i hi)] at hw
    exact (RationalAccumulator.zero_word_iff_blank _ _).mp hw
  · have hg := PhaseMachine.allIds_ge i hi
    have hextra : i∉extraIds∪NaturalQuotient.workPorts := by
      simp only [PhaseMachine.allIds,PhaseMachine.ids,Machin.allIds,RationalArctan.ids,
        RationalMagnitude.ids,RationalTaylor.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
      simp only [extraIds,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      omega
    have h4 : i≠4 := by
      intro he
      subst i
      exact (by decide : 4∉PhaseMachine.allIds) hi
    have hout : i∉workspace S := by
      simp only [workspace,allIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hextra ⊢
      have hsmall : ¬(i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4) := by omega
      tauto
    exact RationalAccumulator.blank_of_eq (f.tapes i hout) (h i hi)

#print axioms Clean.phase_frame
#print axioms phase_clean
end Maxwell.Continuum.RationalDataflow.DyadicFloor
