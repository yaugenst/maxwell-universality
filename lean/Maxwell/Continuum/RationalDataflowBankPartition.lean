import Maxwell.Continuum.RationalDataflowBankCongruence

/-! Joining an updated register region with stored registers preserved by
an executed subprogram. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator

theorem Ready.restrict {S T : Finset ℕ} {v : ℕ→Parts} {s : Store}
    (h : Ready T v s) (hst : S⊆T) : Ready S v s := by
  refine ⟨?_,h.2⟩
  intro i hi
  apply h.1 i
  rcases Finset.mem_union.mp hi with hp|hw
  · obtain ⟨k,hk,hi⟩ := Finset.mem_biUnion.mp hp
    exact cell_mem (hst hk) hi
  · exact Finset.mem_union_right _ hw

theorem Ready.partition {S T : Finset ℕ} {u v : ℕ→Parts} {s t : Store}
    (hsmall : Ready S u t) (hlarge : Ready T v s)
    (hf : ∀j∈T,j∉S → ∀i∈cellPorts j,t.val.tapes i=s.val.tapes i) :
    Ready T (fun j => if j∈S then u j else v j) t := by
  refine ⟨?_,hsmall.2⟩
  intro i hi
  rcases Finset.mem_union.mp hi with hp|hw
  · obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hp
    by_cases hjs : j∈S
    · have h := hsmall.1 i (cell_mem hjs hij)
      simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hij
      rcases hij with rfl|rfl|rfl <;>
        simpa only [dataValues_positive,dataValues_negative,dataValues_denominator,ite_eq_left hjs] using h
    · have h := word_of_eq (hf j hj hjs i hij) (hlarge.1 i (cell_mem hj hij))
      simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hij
      rcases hij with rfl|rfl|rfl <;>
        simpa only [dataValues_positive,dataValues_negative,dataValues_denominator,ite_eq_right hjs] using h
  · have h := hsmall.1 i (Finset.mem_union_right _ hw)
    have hlt : i<1000 := by
      simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hw
      omega
    simpa only [dataValues_small _ hlt] using h

#print axioms Ready.partition
end Maxwell.Continuum.RationalDataflow
