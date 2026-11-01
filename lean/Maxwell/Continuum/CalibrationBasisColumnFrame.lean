import Maxwell.Continuum.CalibrationBasisMatrixLoop

/-! The canonical column boundary is confined below tape6000. It survives
an isolated central test once shared arithmetic scratch is returned. -/
namespace Maxwell.Continuum.Calibration.BasisColumn
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open BasisForcing ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount

theorem bank_bound (k : ℕ) (hk : k∈ids BasisScalarReload.bank) : 4≤k ∧ k<6000 := by
  refine ⟨ids_ge _ _ hk,?_⟩
  exact BasisReentry.changed_bound k (Finset.mem_union_right _ (Finset.mem_union_right _ hk))

theorem allocation_bound (k : ℕ) (hk : k∈allocationIds) : 4≤k ∧ k<6000 := by
  rcases Finset.mem_union.mp hk with natural | allocator
  · rcases Finset.mem_union.mp natural with main | quotient
    · rcases Finset.mem_union.mp main with raw | decoder
      · exact bank_bound k (ids_mono Finset.subset_union_left raw)
      · simpa only [ArrayDecodeMachine.ports,Finset.mem_Icc] using
          (show 4≤k ∧ k<6000 by have := Finset.mem_Icc.mp decoder;omega)
    · simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at quotient;omega
  · simp only [Finset.mem_insert,Finset.mem_singleton] at allocator;omega

theorem State.transfer {R heap P : ℕ} {p : ℕ→Parts} {s t : Store} (state : State R heap P p s)
    (keep : ∀k,4≤k→k<6000→t.val.tapes k=s.val.tapes k)
    (scratch : NatAssign.Scratch t.val) : State R heap P p t := by
  have blank (k : ℕ) (lo : 4≤k) (hi : k<6000) :
      RationalAccumulator.Blank s.val k→RationalAccumulator.Blank t.val k :=
    RationalAccumulator.blank_of_eq (keep k lo hi)
  refine ⟨?_,state.good,state.width⟩
  refine ⟨⟨?_,scratch⟩,?_,?_,?_,?_,blank 4 (by decide) (by decide) state.ready.four,
    blank 7 (by decide) (by decide) state.ready.seven,
    blank 37 (by decide) (by decide) state.ready.packing,
    blank 206 (by decide) (by decide) state.ready.inputTemp,
    blank 216 (by decide) (by decide) state.ready.outputTemp,?_,?_,
    BankArray.word_of_eq (keep 201 (by decide) (by decide)) state.ready.counter,?_⟩
  · intro k hk
    exact RationalAccumulator.word_of_eq (keep k (bank_bound k hk).1 (bank_bound k hk).2) (state.ready.parts.1 k hk)
  · intro k hk
    exact RationalAccumulator.word_of_eq (keep k (allocation_bound k hk).1 (allocation_bound k hk).2)
      (state.ready.naturals k hk)
  · intro k hk
    apply RationalAccumulator.word_of_eq (keep k ?_ ?_) (state.ready.extra k hk)
    all_goals simp only [CoefficientInput.extraIds,Finset.mem_union,Finset.mem_Icc] at hk;omega
  · intro k hk
    apply RationalAccumulator.word_of_eq (keep k ?_ ?_) (state.ready.cold k hk)
    all_goals simp only [InverseDescriptor.coldIds,Finset.mem_union,Finset.mem_Icc] at hk;omega
  · exact ⟨scratch 0 (by decide),scratch 1 (by decide),scratch 2 (by decide),scratch 3 (by decide),
      blank 5 (by decide) (by decide) state.ready.scratch.2.2.2.2.1,
      blank 6 (by decide) (by decide) state.ready.scratch.2.2.2.2.2.1,
      blank 8 (by decide) (by decide) state.ready.scratch.2.2.2.2.2.2.1,
      blank 9 (by decide) (by decide) state.ready.scratch.2.2.2.2.2.2.2⟩
  · intro k hk
    obtain ⟨bits,width,word⟩:=state.ready.outputHeaders k hk
    refine ⟨bits,width,BankArray.word_of_eq (keep k ?_ ?_) word⟩
    all_goals simp only [PowerMachine.BufferNorm.Allocation.clearHeaders,List.mem_cons,List.not_mem_nil,or_false] at hk;omega
  · intro k hk
    obtain ⟨bits,width,word⟩:=state.ready.inputHeaders k hk
    refine ⟨bits,width,BankArray.word_of_eq (keep k ?_ ?_) word⟩
    all_goals simp only [PartArray.Promote.headers,List.mem_cons,List.not_mem_nil,or_false] at hk;omega

  · intro k hk
    have bound:=BasisReentry.cleanup_bounds k hk
    exact blank k (by omega) (by omega) (state.ready.cleared k hk)

#print axioms State.transfer
end Maxwell.Continuum.Calibration.BasisColumn
