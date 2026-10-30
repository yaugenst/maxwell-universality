import Maxwell.Continuum.CalibrationRootGridSample

/-! Frame facts for adjoining the natural grid decoder to the shared
rational elementary machines. The decoder's private words are disjoint. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2500000

def decodeWorkspace : Finset ℕ := {0,1,2,3,4}∪ids
def sampleWorkspace (S : Finset ℕ) : Finset ℕ := decodeWorkspace∪RootProduct.workspace S

theorem ids_bounds (i : ℕ) (hi : i∈ids) : 220 ≤ i ∧ i≤341 := by
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

theorem ids_outside_product (S : Finset ℕ) (i : ℕ) (hi : i∈ids) :
    i∉RootProduct.workspace S := by
  have hr := ids_outside_rational S i hi
  have hg := ids_outside_glue i hi
  have hp := ids_outside_phase i hi
  simp only [RootProduct.workspace,Glue.workspace,Glue.allIds,Phase.Runtime.workspace,
    Phase.Runtime.allIds,RationalDataflow.workspace,Finset.mem_union] at *
  tauto

theorem rationalReady_decode {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : Ready S v s) (f : BinaryPrecision.Frame decodeWorkspace s.val t.val)
    (hz : ∀i,i<5 → Blank t.val i) : Ready S v t := by
  refine ⟨?_,fun i hi => hz i (by omega)⟩
  intro i hi
  have hge := ids_ge_ten S i hi
  have hout : i∉decodeWorkspace := by
    intro hm
    rcases Finset.mem_union.mp hm with hm|hm
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      omega
    · exact ids_outside_rational S i hm (Finset.mem_union_right _ hi)
  exact word_of_eq (f.tapes i hout) (h.1 i hi)

theorem glueClean_decode {s t : Store} (h : Glue.Clean s.val)
    (f : BinaryPrecision.Frame decodeWorkspace s.val t.val)
    (hz : ∀i,i<5 → Blank t.val i) : Glue.Clean t.val := by
  intro i hi
  by_cases hs : i<5
  · exact hz i hs
  have hg := Finset.mem_of_mem_erase hi
  have hout : i∉decodeWorkspace := by
    intro hm
    rcases Finset.mem_union.mp hm with hm|hm
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      omega
    · exact ids_outside_glue i hm hg
  exact blank_of_eq (f.tapes i hout) (h i hi)

theorem phaseClean_decode {s t : Store} (h : Phase.Runtime.Clean s.val)
    (f : BinaryPrecision.Frame decodeWorkspace s.val t.val)
    (hz : ∀i,i<5 → Blank t.val i) : Phase.Runtime.Clean t.val := by
  intro i hi
  by_cases hs : i<5
  · exact hz i hs
  have hp := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
  have hout : i∉decodeWorkspace := by
    intro hm
    rcases Finset.mem_union.mp hm with hm|hm
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      omega
    · exact ids_outside_phase i hm hp
  exact blank_of_eq (f.tapes i hout) (h i hi)

theorem four_outside_product (S : Finset ℕ) : 4∉RootProduct.workspace S := by
  have hg : 4∉GlueMachine.Runtime.ids := by decide
  have hp : 4∉PhaseMachine.Runtime.ids := by decide
  have hr : 4∉RationalDataflow.ids S := by
    simp only [RationalDataflow.ids,Finset.mem_union,not_or]
    exact ⟨RootSample.small_not_ports S 4 (by decide),by decide⟩
  simp only [RootProduct.workspace,Glue.workspace,Glue.allIds,Phase.Runtime.workspace,
    Phase.Runtime.allIds,Finset.mem_union,not_or]
  exact ⟨⟨by decide,hr,hg⟩,by decide,hr,hp⟩

theorem rational_subset_product (S : Finset ℕ) :
    RationalDataflow.workspace S⊆RootProduct.workspace S := by
  intro i hi
  apply Finset.mem_union_left
  rcases Finset.mem_union.mp hi with hi|hi
  · exact Finset.mem_union_left _ hi
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ hi)

#print axioms rationalReady_decode
#print axioms ids_outside_product
end Maxwell.Continuum.RationalDataflow.RootGrid
