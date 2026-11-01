import Maxwell.Continuum.WellStrengthInitializeData

namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Blank Word)
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

private theorem bounded_frame {xs : List ℕ} {H : ℕ} {s t : BitRAMState} {work : Finset ℕ}
    (h : WordCleanup.Bounded xs H s) (f : BinaryPrecision.Frame work s t)
    (outside : ∀i∈xs,i∉work) : WordCleanup.Bounded xs H t:=by
  intro i hi
  obtain ⟨bits,hlen,hw⟩:=h i hi
  exact ⟨bits,hlen,BankArray.word_of_eq (f.tapes i (outside i hi)) hw⟩

structure Result (v : ℕ→ℕ) (parts : ℕ→Parts) (clock : List Bool)
    (memory : ℕ→Bool) (s : Store) : Prop where
  table : (Table.table (Geometry.values v) memory).OutputReady s
  geometry : NatAssign.Bank Geometry.targets (Geometry.values v) s.val
  clockWord : BankArray.Word s.val 962 clock
  rational : Ready WellStrength.bank parts s
  clean : DyadicFloor.Clean s.val
  power : Word s.val 144 (v 144)
  precision : Word s.val 990 (v 990)
  outer : Blank s.val 972
  inner : Blank s.val 973

theorem executes (v : ℕ→ℕ) (parts : ℕ→Parts) (B H : ℕ) (hB : 54≤B)
    (width : ∀i∈inputs,(v i).bits.length≤B)
    (clock : List Bool) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank inputs v s.val) (scratch : BankArray.Scratch s.val)
    (rational : Ready WellStrength.bank parts s)
    (seven : Blank s.val 7) (thirtySeven : Blank s.val 37) (temp : Blank s.val 216)
    (clockWord : BankArray.Word s.val 1251 clock)
    (oldGeometry : WordCleanup.Bounded Geometry.clearHeaders H s.val)
    (oldTable : WordCleanup.Bounded Table.clearHeaders H s.val)
    (oldAllocation : WordCleanup.Bounded Table.Allocation.clearHeaders H s.val)
    (oldClean : WordCleanup.Bounded cleanHeaders H s.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound v B H clock.length ∧
      Result v parts clock s.val.memory t ∧ BinaryPrecision.Frame work s.val t.val:=by
  have gsub : Geometry.inputs⊆inputs:=Finset.subset_union_left
  obtain ⟨c0,a,e0,h0,ba,wa,za,ca,oa,ia,f0⟩:=Geometry.executes v B H hB
    (fun i hi=>width i (gsub hi)) clock input tape s (fun i hi=>bank i (gsub hi)) scratch oldGeometry clockWord
  have sourceBank : NatAssign.Bank Table.sources.toFinset (Geometry.values v) a.val:=by
    intro i hi
    by_cases ht : i∈Geometry.targets
    · exact ba i (Finset.mem_union_right _ ht)
    · have hs : i∈inputs:=Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi,ht⟩)
      rw [Geometry.values_outside v i ht]
      apply RationalAccumulator.word_of_eq (f0.tapes i ?_) (bank i hs)
      have low:=inputs_ge i hs
      have excluded : i≠962 ∧ i≠972 ∧ i≠973:=by
        have disjoint : Disjoint Table.sources.toFinset ({962,972,973}:Finset ℕ):=by decide
        have := Finset.disjoint_left.mp disjoint hi
        simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using this
      simp only [Geometry.work,Finset.mem_union,not_or]
      refine ⟨⟨?_,ht⟩,?_⟩
      · simp only [Finset.mem_insert,Finset.mem_singleton,not_or];omega
      · simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using excluded
  have sourceWidth : ∀i∈Table.sources,(Geometry.values v i).bits.length≤2^30*(B+1):=by
    intro i hi
    by_cases ht : i∈Geometry.targets
    · exact wa i (Finset.mem_union_right _ ht)
    · rw [Geometry.values_outside v i ht]
      have bound:=width i (Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨by simpa only [List.mem_toFinset] using hi,ht⟩))
      have grow : B≤2^30*(B+1):=by omega
      exact bound.trans grow
  have tableOldA := bounded_frame oldTable f0 (by decide)
  have allocationOldA := bounded_frame oldAllocation f0 (by decide)
  obtain ⟨c1,b,e1,h1,tb,_,_,f1⟩:=Table.executes (Geometry.values v) (2^30*(B+1)) H (by omega)
    sourceWidth input tape a sourceBank za
    (RationalAccumulator.blank_of_eq (f0.tapes 7 (by decide)) seven)
    (RationalAccumulator.blank_of_eq (f0.tapes 37 (by decide)) thirtySeven)
    (RationalAccumulator.blank_of_eq (f0.tapes 216 (by decide)) temp) tableOldA allocationOldA
  have f01 : BinaryPrecision.Frame (Geometry.work∪Table.work) s.val b.val:=
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)
  have cleanOldB:=bounded_frame oldClean f01 (by decide)
  obtain ⟨c2,t,e2,h2,zt,f2⟩:=WordCleanup.executes cleanHeaders H input tape b cleanOldB
  have frame : BinaryPrecision.Frame work s.val t.val:=
    (f01.mono Finset.subset_union_left).trans (f2.mono Finset.subset_union_right)
  have scratchT : BankArray.Scratch t.val:=by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact RationalAccumulator.blank_of_eq (f2.tapes 0 (by decide)) tb.scratch.1
    · exact RationalAccumulator.blank_of_eq (f2.tapes 1 (by decide)) tb.scratch.2.1
    · exact RationalAccumulator.blank_of_eq (f2.tapes 2 (by decide)) tb.scratch.2.2.1
    · exact RationalAccumulator.blank_of_eq (f2.tapes 3 (by decide)) tb.scratch.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (f2.tapes 5 (by decide)) tb.scratch.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (f2.tapes 6 (by decide)) tb.scratch.2.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (f2.tapes 8 (by decide)) tb.scratch.2.2.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (f2.tapes 9 (by decide)) tb.scratch.2.2.2.2.2.2.2
  have sevenT := RationalAccumulator.blank_of_eq (frame.tapes 7 (by decide)) seven
  have readyT : Ready WellStrength.bank parts t:=by
    constructor
    · intro i hi
      have outside : i∉work:=by
        have disjoint : Disjoint (RationalDataflow.ids WellStrength.bank) work:=by decide
        exact Finset.disjoint_left.mp disjoint hi
      exact RationalAccumulator.word_of_eq (frame.tapes i outside) (rational.1 i hi)
    · intro i hi
      interval_cases i
      · exact scratchT.1
      · exact scratchT.2.1
      · exact scratchT.2.2.1
      · exact scratchT.2.2.2.1
  have tableT : (Table.table (Geometry.values v) s.val.memory).OutputReady t:=by
    rw [←f0.memory]
    exact tb.transfer f2.memory (by
      intro i hi
      apply f2.tapes
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide) scratchT sevenT
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,?_,frame⟩
  · unfold costBound
    omega
  · refine ⟨tableT,?_,?_,readyT,?_,?_,?_,?_,?_⟩
    · intro i hi
      have outside : i∉Table.work ∧ i∉cleanHeaders.toFinset:=by
        have d1 : Disjoint Geometry.targets Table.work:=by decide
        have d2 : Disjoint Geometry.targets cleanHeaders.toFinset:=by decide
        exact ⟨Finset.disjoint_left.mp d1 hi,Finset.disjoint_left.mp d2 hi⟩
      exact RationalAccumulator.word_of_eq ((f2.tapes i outside.2).trans (f1.tapes i outside.1))
        (ba i (Finset.mem_union_right _ hi))
    · exact BankArray.word_of_eq ((f2.tapes 962 (by decide)).trans (f1.tapes 962 (by decide))) ca
    · refine ⟨zt 4 (by decide),?_⟩
      intro i hi
      apply zt
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with (rfl|rfl|rfl)|(rfl|rfl|rfl|rfl) <;> decide
    · exact RationalAccumulator.word_of_eq (frame.tapes 144 (by decide)) (bank 144 (by decide))
    · exact RationalAccumulator.word_of_eq (frame.tapes 990 (by decide)) (bank 990 (by decide))
    · exact RationalAccumulator.blank_of_eq ((f2.tapes 972 (by decide)).trans (f1.tapes 972 (by decide))) oa
    · exact RationalAccumulator.blank_of_eq ((f2.tapes 973 (by decide)).trans (f1.tapes 973 (by decide))) ia

#print axioms executes
end Maxwell.Continuum.WellStrengthInitialization
