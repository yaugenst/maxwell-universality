import Maxwell.Continuum.CalibrationBasisSchurColumn
import Maxwell.Continuum.CalibrationBasisScalarReload

/-! The exact canonical state for another basis column. Only the stored
radius, free heap, and five physical scalars survive the charged cleanup. -/
namespace Maxwell.Continuum.Calibration.BasisReentry
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow PartArray ArrayDecodeMachine NeumannMachine BasisForcing
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount

def cleanupWords : List ℕ := Descriptors.retainedIds.sort (·≤·)++
  (Finset.Icc 312 332).sort (·≤·)++conversionRetiredWords++
  CoefficientAllocation.workIds.sort (·≤·)++AllocatedInverse.inactiveIds.sort (·≤·)++
  Horner.activeCleanup++SchurReadColumn.readoutWords

def numbers (R heap : ℕ) (p : ℕ→Parts) (k : ℕ) : ℕ :=
  if k=311 then R else if k=376 then heap else dataValues (BasisScalarReload.values p) k

structure InputReady (R heap : ℕ) (p : ℕ→Parts) (s : Store) : Prop where
  parts : Ready BasisScalarReload.bank (BasisScalarReload.values p) s
  naturals : NatAssign.Bank allocationIds (numbers R heap p) s.val
  extra : NatAssign.Bank CoefficientInput.extraIds (fun _=>0) s.val
  cold : NatAssign.Bank InverseDescriptor.coldIds (fun _=>0) s.val
  scratch : BankArray.Scratch s.val
  four : RationalAccumulator.Blank s.val 4
  seven : RationalAccumulator.Blank s.val 7
  packing : RationalAccumulator.Blank s.val 37
  inputTemp : RationalAccumulator.Blank s.val 206
  outputTemp : RationalAccumulator.Blank s.val 216
  outputHeaders : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders 0 s.val
  inputHeaders : WordCleanup.Bounded Promote.headers 0 s.val
  counter : BankArray.Word s.val 201 []
  cleared : ∀k∈cleanupWords,RationalAccumulator.Blank s.val k

theorem cleanup_bounds : ∀k∈cleanupWords,
    (k=4 ∨ k=37 ∨ 107≤k) ∧ k<600 ∧ k≠311 ∧ k≠376 := by
  intro k hk
  simp only [cleanupWords,List.mem_append,Finset.mem_sort,Descriptors.retainedIds,
    Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton,
    conversionRetiredWords,retiredWords,List.mem_cons,List.not_mem_nil,or_false,
    CoefficientAllocation.workIds,AllocatedInverse.inactiveIds,Horner.activeCleanup,
    Horner.workCleanup,Horner.portCleanup,SchurReadColumn.readoutWords,List.mem_range'_1] at hk
  omega

theorem cleanup_cover (k : ℕ)
    (hk : k=4 ∨ k=37 ∨ (107≤k ∧ k≤140) ∨ (200≤k ∧ k≤206) ∨
      k=210 ∨ (212≤k ∧ k≤216) ∨ (220≤k ∧ k≤223) ∨ (300≤k ∧ k≤310) ∨
      (312≤k ∧ k≤332) ∨ (530≤k ∧ k≤534) ∨ (570≤k ∧ k≤573) ∨ (580≤k ∧ k≤584)) :
    k∈cleanupWords := by
  simp only [cleanupWords,List.mem_append,Finset.mem_sort,Descriptors.retainedIds,
    Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton,
    conversionRetiredWords,retiredWords,List.mem_cons,List.not_mem_nil,or_false,
    CoefficientAllocation.workIds,AllocatedInverse.inactiveIds,Horner.activeCleanup,
    Horner.workCleanup,Horner.portCleanup,SchurReadColumn.readoutWords,List.mem_range'_1]
  omega

theorem cleanup_workspace (k : ℕ) (hk : k∈cleanupWords) : k∉workspace BasisScalarReload.bank := by
  obtain ⟨low,high,_,_⟩:=cleanup_bounds k hk
  simp only [workspace,ids,Finset.mem_union,not_or]
  refine ⟨by simp only [Finset.mem_insert,Finset.mem_singleton];omega,?_,?_⟩
  · intro h
    obtain ⟨i,_,cell⟩:=Finset.mem_biUnion.mp h
    simp only [cellPorts,positivePort,negativePort,denominatorPort,
      Finset.mem_insert,Finset.mem_singleton] at cell
    omega
  · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton];omega

theorem numbers_agree (R heap : ℕ) (p : ℕ→Parts) (k : ℕ) (hk : k∈ids BasisForcing.bank) :
    numbers R heap p k=dataValues (BasisScalarReload.values p) k := by
  have outside : k≠311 ∧ k≠376 := by
    rcases Finset.mem_union.mp hk with raw|work
    · obtain ⟨i,_,cell⟩:=Finset.mem_biUnion.mp raw
      simp only [cellPorts,positivePort,negativePort,denominatorPort,
        Finset.mem_insert,Finset.mem_singleton] at cell
      omega
    · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at work
      omega
  simp only [numbers,ite_eq_right outside.1,ite_eq_right outside.2]

theorem radius (R heap : ℕ) (p : ℕ→Parts) : numbers R heap p 311=R := by simp [numbers]
theorem heap (R h : ℕ) (p : ℕ→Parts) : numbers R h p 376=h := by simp [numbers]

theorem assemble (R h : ℕ) (p : ℕ→Parts) (s : Store)
    (parts : Ready BasisScalarReload.bank (BasisScalarReload.values p) s)
    (cleared : ∀k∈cleanupWords,RationalAccumulator.Blank s.val k)
    (rad : RationalAccumulator.Word s.val 311 R)
    (free : RationalAccumulator.Word s.val 376 h)
    (scratch : BankArray.Scratch s.val) (seven : RationalAccumulator.Blank s.val 7) :
    InputReady R h p s := by
  have zero : ∀k∈cleanupWords,RationalAccumulator.Word s.val k 0 :=
    fun k hk=>(RationalAccumulator.zero_word_iff_blank _ _).mpr (cleared k hk)
  refine ⟨parts,?_,?_,?_,scratch,cleared 4 (cleanup_cover _ (by omega)),seven,
    cleared 37 (cleanup_cover _ (by omega)),cleared 206 (cleanup_cover _ (by omega)),
    cleared 216 (cleanup_cover _ (by omega)),?_,?_,?_,cleared⟩
  · intro k hk
    by_cases atRadius : k=311
    · subst k;simpa only [radius] using rad
    by_cases atHeap : k=376
    · subst k;simpa only [heap] using free
    rw [numbers,ite_eq_right atRadius,ite_eq_right atHeap]
    by_cases raw : k∈ids BasisForcing.bank
    · exact parts.1 k (ids_mono Finset.subset_union_left raw)
    · have rest : (310≤k ∧ k≤320) ∨ (220≤k ∧ k≤223) ∨
          k=376 ∨ (570≤k ∧ k≤573) := by
        rcases Finset.mem_union.mp hk with natural | allocator
        · rcases Finset.mem_union.mp natural with main | quotient
          · rcases Finset.mem_union.mp main with cell | decoder
            · exact (raw cell).elim
            · simpa only [ArrayDecodeMachine.ports,Finset.mem_Icc] using Or.inl decoder
          · simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at quotient
            omega
        · simp only [Finset.mem_insert,Finset.mem_singleton] at allocator
          omega
      rw [dataValues_small _ (by omega : k<1000)]
      exact zero k (cleanup_cover k (by omega))
  · intro k hk
    apply zero k (cleanup_cover k ?_)
    simp only [CoefficientInput.extraIds,Finset.mem_union,Finset.mem_Icc] at hk
    omega
  · intro k hk
    apply zero k (cleanup_cover k ?_)
    simp only [InverseDescriptor.coldIds,Finset.mem_union,Finset.mem_Icc] at hk
    omega
  · intro k hk
    refine ⟨[],Nat.le_refl _,?_⟩
    apply zero k (cleanup_cover k ?_)
    simp only [PowerMachine.BufferNorm.Allocation.clearHeaders,List.mem_cons,
      List.not_mem_nil,or_false] at hk
    omega
  · intro k hk
    refine ⟨[],Nat.le_refl _,?_⟩
    apply zero k (cleanup_cover k ?_)
    simp only [Promote.headers,List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
  · exact zero 201 (cleanup_cover _ (by omega))

#print axioms assemble
#print axioms cleanup_workspace
#print axioms numbers_agree
end Maxwell.Continuum.Calibration.BasisReentry
