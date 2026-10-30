import Maxwell.Continuum.ChebyshevWaveRuntimeCosineData

/-! The saved Fourier words and loop metadata are disjoint from every actual
phase, floor, and shared-arithmetic workspace. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 2000000

def savedPorts : Finset ℕ := StoredParts.ports 690∪StoredParts.ports 693
def cosineWorkspace : Finset ℕ := sumWorkspace∪savedPorts

theorem LoopReady.external_frame {Q P : ℕ} {v : ℕ→Parts} {s t : Store} {changed : Finset ℕ}
    (h : LoopReady Q P v s) (f : BinaryPrecision.Frame changed s.val t.val)
    (hc : ∀i∈changed,680 ≤ i ∧ i<1000) : LoopReady Q P v t := by
  have keepSmall (i : ℕ) (hi : i<680) : t.val.tapes i=s.val.tapes i :=
    f.tapes i (by intro hm;have hh := hc i hm;omega)
  refine ⟨⟨?_,?_⟩,?_,⟨?_,?_⟩,?_,word_of_eq (keepSmall 652 (by decide)) h.rangeWord,
    word_of_eq (keepSmall 653 (by decide)) h.precisionWord⟩
  · intro i hi
    apply word_of_eq (f.tapes i _) (h.ready.1 i hi)
    intro hm
    have hh := hc i hm
    exact (RationalDataflow.outside_workspace ids i (by omega)) (Finset.mem_union_right _ hi)
  · intro i hi
    exact blank_of_eq (keepSmall i (by omega)) (h.ready.2 i hi)
  · intro i hi
    have hp : i∈PhaseMachine.Runtime.ids := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
    apply blank_of_eq (f.tapes i _) (h.phase i hi)
    intro hm
    have hh := hc i hm
    exact (Phase.Runtime.metadata_outside_workspace ids i (by omega))
      (Finset.mem_union_right _ (Finset.mem_union_right _ hp))
  · exact blank_of_eq (keepSmall 4 (by decide)) h.floor.1
  · intro i hi
    have hil : i<680 := by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact blank_of_eq (keepSmall i hil) (h.floor.2 i hi)
  · intro i hi
    have hh := parameterIds_range i hi
    exact word_of_eq (keepSmall i (by omega)) (h.parameters i hi)

theorem savedPorts_range (i : ℕ) (hi : i∈savedPorts) : 690 ≤ i ∧ i ≤ 695 := by
  simp only [savedPorts,StoredParts.ports,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem savedPorts_disjoint_sum : Disjoint savedPorts sumWorkspace := by
  apply Finset.disjoint_left.mpr
  intro i hi hm
  have hh := savedPorts_range i hi
  rcases Finset.mem_insert.mp hm with hm|hm
  · omega
  · rcases Finset.mem_union.mp hm with hm|hm
    · exact (Phase.Runtime.metadata_outside_workspace ids i (by omega)) hm
    · exact (DyadicFloor.high_outside_workspace ids i (by omega)) hm

theorem arithmetic_subset_cosine : RationalDataflow.workspace ids⊆cosineWorkspace :=
  arithmetic_subset_evaluation.trans ((Finset.subset_insert _ _).trans Finset.subset_union_left)

theorem saved_base_subset (base : ℕ) (hb : base=690 ∨ base=693) :
    StoredParts.ports base⊆savedPorts := by
  rcases hb with rfl|rfl
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

theorem stored_sum_frame {base : ℕ} (hb : base=690 ∨ base=693) {x : Parts} {s t : Store}
    (h : StoredParts.Stored base x s.val) (f : BinaryPrecision.Frame sumWorkspace s.val t.val) :
    StoredParts.Stored base x t.val :=
  h.frame f (savedPorts_disjoint_sum.mono_left (saved_base_subset base hb))

theorem word681_sum_frame {s t : Store} {grid : ℕ} (h : Word s.val 681 grid)
    (f : BinaryPrecision.Frame sumWorkspace s.val t.val) : Word t.val 681 grid := by
  apply word_of_eq (f.tapes 681 _) h
  simp only [sumWorkspace,Finset.mem_insert]
  refine not_or_intro (by decide) ?_
  exact fun hm => (Finset.mem_union.mp hm).elim
    (Phase.Runtime.metadata_outside_workspace ids 681 (by decide))
    (DyadicFloor.high_outside_workspace ids 681 (by decide))

#print axioms LoopReady.external_frame
#print axioms savedPorts_disjoint_sum
end Maxwell.Continuum.Profile.WaveMachine.Runtime
