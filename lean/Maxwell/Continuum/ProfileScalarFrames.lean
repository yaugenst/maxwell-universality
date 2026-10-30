import Maxwell.Continuum.PhaseRuntimeDataflowExecution
import Maxwell.Continuum.GlueDataflowCost

/-! Cleanup joins for repeated fixed phase and glue calls in the profile
producer. Shared arithmetic may use their overlapping temporary registers. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000

private theorem blank_transfer (S T B A : Finset ℕ) (v : ℕ→Parts) (s t : Store)
    (hT : ∀ i ∈ T, 4 ≤ i ∧ i < 1000) (hcover : ∀ i ∈ T, i ∈ B → i ∈ A)
    (hz : ∀i∈T,Blank s.val i) (hd : ∀i∈A,Blank t.val i)
    (hr : Ready S v t)
    (hf : BinaryPrecision.Frame ({0,1,2,3}∪(ids S∪B)) s.val t.val) :
    ∀i∈T,Blank t.val i := by
  intro i hi
  obtain ⟨hg,hs⟩ := hT i hi
  by_cases hm : i∈ids S
  · have hw := hr.1 i hm
    rw [dataValues_small v hs] at hw
    exact (zero_word_iff_blank _ _).mp hw
  by_cases hb : i∈B
  · exact hd i (hcover i hi hb)
  · apply blank_of_eq (hf.tapes i _) (hz i hi)
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    exact not_or_intro (by omega) (not_or_intro hm hb)

theorem phaseClean_arithmetic {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (hz : Phase.Runtime.Clean s.val) (hr : Ready S v t)
    (hf : BinaryPrecision.Frame (RationalDataflow.workspace S) s.val t.val) :
    Phase.Runtime.Clean t.val := by
  apply blank_transfer S ((PhaseMachine.Runtime.ids.erase 652).erase 653) ∅ ∅ v s t
    (fun i hi => ⟨PhaseMachine.Runtime.ids_ge i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)),
      Phase.Runtime.ids_small i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))⟩)
    (by simp) hz (by simp) hr
  simpa only [RationalDataflow.workspace,Finset.union_empty] using hf

theorem glueClean_arithmetic {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (hz : Glue.Clean s.val) (hr : Ready S v t)
    (hf : BinaryPrecision.Frame (RationalDataflow.workspace S) s.val t.val) :
    Glue.Clean t.val := by
  apply blank_transfer S (GlueMachine.Runtime.ids.erase 640) ∅ ∅ v s t
    (fun i hi => ⟨GlueMachine.Runtime.ids_ge i (Finset.mem_of_mem_erase hi),
      Glue.ids_small i (Finset.mem_of_mem_erase hi)⟩) (by simp) hz (by simp) hr
  simpa only [RationalDataflow.workspace,Finset.union_empty] using hf

theorem glueClean_after_phase {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (hz : Glue.Clean s.val) (hd : Phase.Runtime.Clean t.val) (hr : Ready S v t)
    (hf : BinaryPrecision.Frame (Phase.Runtime.workspace S) s.val t.val) :
    Glue.Clean t.val := by
  apply blank_transfer S (GlueMachine.Runtime.ids.erase 640) PhaseMachine.Runtime.ids
    ((PhaseMachine.Runtime.ids.erase 652).erase 653) v s t
    (fun i hi => ⟨GlueMachine.Runtime.ids_ge i (Finset.mem_of_mem_erase hi),
      Glue.ids_small i (Finset.mem_of_mem_erase hi)⟩) ?_ hz hd hr hf
  intro i hi hb
  have hn : i≠652 ∧ i≠653 := by
    constructor <;> intro he <;> subst i
    · exact (show (652:ℕ)∉GlueMachine.Runtime.ids by decide) (Finset.mem_of_mem_erase hi)
    · exact (show (653:ℕ)∉GlueMachine.Runtime.ids by decide) (Finset.mem_of_mem_erase hi)
  exact Finset.mem_erase.mpr ⟨hn.2,Finset.mem_erase.mpr ⟨hn.1,hb⟩⟩

theorem phaseClean_after_glue {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (hz : Phase.Runtime.Clean s.val) (hd : Glue.Clean t.val) (hr : Ready S v t)
    (hf : BinaryPrecision.Frame (Glue.workspace S) s.val t.val) :
    Phase.Runtime.Clean t.val := by
  apply blank_transfer S ((PhaseMachine.Runtime.ids.erase 652).erase 653) GlueMachine.Runtime.ids
    (GlueMachine.Runtime.ids.erase 640) v s t
    (fun i hi => ⟨PhaseMachine.Runtime.ids_ge i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)),
      Phase.Runtime.ids_small i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))⟩) ?_ hz hd hr hf
  intro i hi hb
  have hn : i≠640 := by
    intro he
    subst i
    exact (show (640:ℕ)∉PhaseMachine.Runtime.ids by decide)
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
  exact Finset.mem_erase.mpr ⟨hn,hb⟩

theorem phase_preserves_glue_precision (S : Finset ℕ) (s t : Store)
    (hf : BinaryPrecision.Frame (Phase.Runtime.workspace S) s.val t.val) (N : ℕ)
    (hn : Word s.val 640 N) : Word t.val 640 N := by
  apply word_of_eq (hf.tapes 640 _) hn
  have hsmall := Glue.precision_outside S
  simp only [Phase.Runtime.workspace,Phase.Runtime.allIds,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton]
  exact not_or_intro (by decide) (not_or_intro hsmall (by decide))

theorem glue_preserves_phase_parameter (S : Finset ℕ) (s t : Store)
    (hf : BinaryPrecision.Frame (Glue.workspace S) s.val t.val) (i N : ℕ)
    (hi : i=652 ∨ i=653) (hn : Word s.val i N) : Word t.val i N := by
  apply word_of_eq (hf.tapes i _) hn
  have hsmall := Phase.Runtime.parameter_outside S i hi
  have hglue : i∉GlueMachine.Runtime.ids := by
    rcases hi with rfl|rfl <;> decide
  simp only [Glue.workspace,Glue.allIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  exact not_or_intro (by omega) (not_or_intro hsmall hglue)

#print axioms glueClean_after_phase
#print axioms phaseClean_after_glue
end Maxwell.Continuum.Profile.Runtime
