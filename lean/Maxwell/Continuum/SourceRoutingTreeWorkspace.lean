import Maxwell.Continuum.SourceRoutingPrivateVisit

/-! The routing tree has one finite set of blank reusable work tapes.
Arithmetic on the separate tree controls preserves this invariant. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Workspace
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def small : Finset ℕ := {0,1,2,3,5,6,7,8,9,37}
def raw : Finset ℕ := small∪NodeCleanup.banks.toFinset
def ids : Finset ℕ := small∪PrivateNode.banks.toFinset

theorem raw_iff (s : BitRAMState) : NodeVisit.Clean s ↔ ∀i∈raw,Blank s i := by
  constructor
  · rintro ⟨work,bank⟩ i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · simp only [small,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact work.1.1.1
      · exact work.1.1.2.1
      · exact work.1.1.2.2.1
      · exact work.1.1.2.2.2.1
      · exact work.1.1.2.2.2.2.1
      · exact work.1.1.2.2.2.2.2.1
      · exact work.1.2.1
      · exact work.1.1.2.2.2.2.2.2.1
      · exact work.1.1.2.2.2.2.2.2.2
      · exact work.2
    · exact bank i (List.mem_toFinset.mp hi)
  · intro hs
    have hsmall (i : ℕ) (hi : i∈small) := hs i (Finset.mem_union_left _ hi)
    have hbank (i : ℕ) (hi : i∈NodeCleanup.banks) := hs i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
    refine ⟨⟨⟨⟨hsmall 0 (by decide),hsmall 1 (by decide),hsmall 2 (by decide),hsmall 3 (by decide),
      hsmall 5 (by decide),hsmall 6 (by decide),hsmall 8 (by decide),hsmall 9 (by decide)⟩,
      hsmall 7 (by decide),?_⟩,hsmall 37 (by decide)⟩,hbank⟩
    intro i hi
    apply hbank i
    dsimp only [DoublingPass.Private] at hi
    simp only [NodeCleanup.banks,List.mem_cons,List.not_mem_nil,or_false]
    omega

theorem small_fixed (i : ℕ) (hi : i∈small) : PrivateNode.shift i=i := by
  apply PrivateNode.shift_small
  simp only [small,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem clean_iff (s : Store) : PrivateVisit.Clean s ↔ ∀i∈ids,Blank s.val i := by
  rw [PrivateVisit.Clean,raw_iff]
  constructor
  · intro hs i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · have hh := hs i (Finset.mem_union_left _ hi)
      simpa only [PrivateNode.relocation_symm,PrivateNode.renamed_tape,small_fixed i hi,
        RationalAccumulator.Blank] using hh
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
      exact hs j (Finset.mem_union_right _ (List.mem_toFinset.mpr hj))
  · intro hs i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · have hh := hs i (Finset.mem_union_left _ hi)
      simpa only [PrivateNode.relocation_symm,PrivateNode.renamed_tape,small_fixed i hi,
        RationalAccumulator.Blank] using hh
    · exact hs (PrivateNode.shift i) (Finset.mem_union_right _ (List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨i,List.mem_toFinset.mp hi,rfl⟩)))

theorem scratch {s : Store} (hs : PrivateVisit.Clean s) : NatAssign.Scratch s.val := by
  intro i hi
  apply (clean_iff s).mp hs i
  apply Finset.mem_union_left
  simp only [small,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem of_frame {s t : Store} {changed : Finset ℕ} (hs : PrivateVisit.Clean s)
    (hz : NatAssign.Scratch t.val) (hf : BinaryPrecision.Frame changed s.val t.val)
    (hkeep : ∀i∈ids,4 ≤ i → i∉changed) : PrivateVisit.Clean t := by
  apply (clean_iff t).mpr
  intro i hi
  by_cases hlo : i<4
  · exact hz i hlo
  · exact RationalAccumulator.blank_of_eq (hf.tapes i (hkeep i hi (by omega))) ((clean_iff s).mp hs i hi)

#print axioms clean_iff
#print axioms of_frame
end Maxwell.Cost.RoutingPorts.Complete.Tree.Workspace
