import Maxwell.Continuum.RationalDataflowLayout

/-! Arithmetic readiness depends only on the tapes in its declared workspace. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured

theorem Ready.transfer_tapes {S : Finset ℕ} {v : ℕ→Parts} {s t : Store} (h : Ready S v s)
    (keep : ∀i∈workspace S,t.val.tapes i=s.val.tapes i) : Ready S v t := by
  refine ⟨fun i hi=>RationalAccumulator.word_of_eq (keep i (Finset.mem_union_right _ hi)) (h.1 i hi),?_⟩
  intro i hi
  apply RationalAccumulator.blank_of_eq (keep i _) (h.2 i hi)
  apply Finset.mem_union_left
  simp only [Finset.mem_insert,Finset.mem_singleton]
  omega

#print axioms Ready.transfer_tapes
end Maxwell.Continuum.RationalDataflow
