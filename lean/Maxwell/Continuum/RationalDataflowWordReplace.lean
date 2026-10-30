import Maxwell.Continuum.RationalDataflowSharedPassFrame

/-! Saved runtime loop counters coexist with the rational register bank. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured

theorem Ready.wordReplace_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store} {target : ℕ}
    (h : Ready S v s) (ht : target∉workspace S)
    (f : WordReplace.Frame target s.val t.val) : Ready S v t := by
  constructor
  · intro i hi
    have hn : i≠target := fun he => ht (he ▸ Finset.mem_union_right _ hi)
    exact RationalAccumulator.word_of_eq (f.2.2.2.2.2.1 i hn) (h.1 i hi)
  · intro i hi
    have hn : i≠target := by
      intro he
      apply ht
      rw [← he]
      apply Finset.mem_union_left
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
    exact RationalAccumulator.blank_of_eq (f.2.2.2.2.2.1 i hn) (h.2 i hi)

#print axioms Ready.wordReplace_frame
end Maxwell.Continuum.RationalDataflow
