import Maxwell.Continuum.RationalDataflowLayout

/-! The shared bank depends only on its declared logical registers. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured

theorem Ready.congr {S : Finset ℕ} {v w : ℕ→Parts} {s : Store}
    (h : Ready S v s) (he : ∀i∈S,v i=w i) : Ready S w s := by
  refine ⟨?_,h.2⟩
  intro i hi
  have hi' := h.1 i hi
  rcases Finset.mem_union.mp hi with hp | hw
  · obtain ⟨r,hr,ht⟩ := Finset.mem_biUnion.mp hp
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · simpa only [dataValues_positive,he r hr] using hi'
    · simpa only [dataValues_negative,he r hr] using hi'
    · simpa only [dataValues_denominator,he r hr] using hi'
  · have hsmall : i<1000 := by
      simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hw
      omega
    simpa only [dataValues_small _ hsmall] using hi'

#print axioms Ready.congr
end Maxwell.Continuum.RationalDataflow
