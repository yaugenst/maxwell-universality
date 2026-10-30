import Maxwell.Continuum.PhaseRuntimeDataflowCode
import Maxwell.Continuum.RationalDataflowWordReplace

/-! Runtime phase calls preserve ordinary arithmetic and external loop metadata. -/
namespace Maxwell.Continuum.RationalDataflow.Phase.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2000000

theorem Clean.arithmetic_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : Clean s.val) (f : BinaryPrecision.Frame (RationalDataflow.workspace S) s.val t.val)
    (hr : RationalDataflow.Ready S v t) : Clean t.val := by
  intro i hi
  have hp : i∈PhaseMachine.Runtime.ids := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
  by_cases hs : i∈RationalDataflow.ids S
  · have hw := hr.1 i hs
    rw [dataValues_small v (ids_small i hp)] at hw
    exact (zero_word_iff_blank _ _).mp hw
  · have hg := PhaseMachine.Runtime.ids_ge i hp
    have ho : i∉RationalDataflow.workspace S := by
      simp only [RationalDataflow.workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      exact not_or_intro (by omega) hs
    exact blank_of_eq (f.tapes i ho) (h i hi)

theorem parameter_outside_workspace (S : Finset ℕ) (i : ℕ) (hi : i=652 ∨ i=653) :
    i∉RationalDataflow.workspace S := by
  have hr := parameter_outside S i hi
  simp only [RationalDataflow.workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  exact not_or_intro (by omega) hr

theorem Clean.wordReplace_frame {s t : Store} {target : ℕ} (ht : target=652 ∨ target=653)
    (h : Clean s.val) (f : WordReplace.Frame target s.val t.val) : Clean t.val := by
  intro i hi
  have h653 := (Finset.mem_erase.mp hi).1
  have h652 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  exact blank_of_eq (f.2.2.2.2.2.1 i (by omega)) (h i hi)

theorem parameter_copy_frame {S : Finset ℕ} {s t : Store} {target : ℕ}
    (ht : target=652 ∨ target=653) (f : WordReplace.Frame target s.val t.val) :
    BinaryPrecision.Frame (workspace S) s.val t.val := by
  refine ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,f.2.2.2.2.1,?_⟩
  intro i hi
  apply f.2.2.2.2.2.1 i
  intro he
  subst i
  apply hi
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  rcases ht with rfl|rfl <;> decide

theorem metadata_outside_workspace (S : Finset ℕ) (i : ℕ) (hi : 658 ≤ i ∧ i<1000) :
    i∉workspace S := by
  have hr : i∉RationalDataflow.ids S := by
    intro hm
    rcases Finset.mem_union.mp hm with hm|hm
    · obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hm
      have hp := positivePort_ge r
      have hn := negativePort_ge r
      have hd := denominatorPort_ge r
      simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hr
      omega
    · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hm
      omega
  have hp : i∉PhaseMachine.Runtime.ids := by
    simp only [PhaseMachine.Runtime.ids,PhaseMachine.Runtime.extras,PhaseMachine.allIds,
      PhaseMachine.ids,Machin.allIds,RationalArctan.ids,RationalTaylor.ids,RationalMagnitude.ids,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega
  simp only [workspace,allIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  exact not_or_intro (by omega) (not_or_intro hr hp)

#print axioms Clean.arithmetic_frame
#print axioms metadata_outside_workspace
end Maxwell.Continuum.RationalDataflow.Phase.Runtime
