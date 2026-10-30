import Maxwell.Continuum.ProfileAngularLoaded

/-! Runtime profile samples preserve the indexed-loop and dimension words. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000

theorem scalar_external (S : Finset ℕ) (i : ℕ)
    (hi : (107 ≤ i ∧ i < 600) ∨ (658 ≤ i ∧ i < 1000)) : i∉angularWorkspace S := by
  have hr := RationalDataflow.outside_workspace S i (by omega)
  have hp : i∉PhaseMachine.Runtime.ids := by
    simp only [PhaseMachine.Runtime.ids,PhaseMachine.Runtime.extras,PhaseMachine.allIds,
      PhaseMachine.ids,Machin.allIds,RationalArctan.ids,RationalTaylor.ids,RationalMagnitude.ids,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega
  have hg : i∉GlueMachine.Runtime.ids := by
    simp only [GlueMachine.Runtime.ids,GlueMachine.ids,GlueMachine.extra,
      SelectedParameters.Compare.ids,RationalTaylor.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega
  simp only [angularWorkspace,Phase.Runtime.workspace,Phase.Runtime.allIds,Glue.workspace,Glue.allIds,
    RationalDataflow.workspace,Finset.mem_union] at hr ⊢
  tauto

theorem arithmetic_sub_scalar (S : Finset ℕ) : RationalDataflow.workspace S⊆angularWorkspace S := by
  intro i hi
  apply Finset.mem_union_left
  rcases Finset.mem_union.mp hi with hi|hi
  · exact Finset.mem_union_left _ hi
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ hi)

#print axioms scalar_external
end Maxwell.Continuum.Profile.Runtime
