import Maxwell.Continuum.CalibrationEdgeScalarRestartData

/-! Run the actual Machin/midpoint scalar producer, clear the previous Schur
bank, and reload the source inputs. Result widths are independent of the old
matrix width; all old-word clearing costs are charged explicitly. -/
namespace Maxwell.Continuum.Calibration.EdgeScalarRestart
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount
  EdgeScalar.resultWidth EdgeScalar.cost Initialize.resetCost BasisReentry.costBound

def cost (N B P : ℕ) : ℕ := EdgeScalar.cost N (max B P)+
  (Initialize.resetCost erased (eraseWidth N B P)+
    BasisReentry.costBound 0 (max 1 P) (max 1 (EdgeScalar.resultWidth N B)))

theorem executes (R heap N B P : ℕ) (mid : Parts) (p : ℕ→Parts)
    (positive : 1≤B) (midGood : 0<mid.denominator) (midWidth : mid.Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (state : BasisColumn.State R heap P p s)
    (precision : RationalAccumulator.Word s.val 850 N) (fresh : EdgeScalar.RelocatedFresh s.val)
    (midpoint : StoredParts.Stored (positivePort 2302) mid s.val) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost N B P ∧
      BasisColumn.State R heap (width N B) (EdgeScalar.result N mid) t ∧
      EdgeScalar.RelocatedFresh t.val ∧
      (∀k,600≤k→k<900→t.val.tapes k=s.val.tapes k) ∧
      (∀k,6000≤k→t.val.tapes k=s.val.tapes k) := by
  let C:=EdgeScalar.resultWidth N B
  obtain ⟨c0,u,e0,b0,scalars,_,scratch0,fresh0,f0⟩:=EdgeScalar.executes N (max B P) mid p
    (midWidth.mono (le_max_left _ _))
    (fun i hi=>(state.schur_width i (EdgeScalar.saved_subset hi)).mono (le_max_right _ _))
    input tape s precision fresh state.ready.parts.2
    (fun i hi=>state.schur_cells i (EdgeScalar.saved_subset hi)) midpoint
  have patched:=EdgeScalar.patched_ready state scalars scratch0 f0
  have rawWidth : WidthBank SchurRow.bank (eraseWidth N B P) (EdgeScalar.patch N mid p) :=
    fun i hi=>(EdgeScalar.patch_width N B P mid p positive midWidth state.schur_width i hi).mono
      (by unfold eraseWidth;omega)
  have keepWidth : WidthBank EdgeScalar.saved C (EdgeScalar.patch N mid p) := by
    intro i hi
    simpa only [EdgeScalar.patch,ite_eq_left hi] using EdgeScalar.result_width N B mid positive midWidth i hi
  have keepGood : Good EdgeScalar.saved (EdgeScalar.patch N mid p) := by
    intro i hi
    simpa only [EdgeScalar.patch,ite_eq_left hi] using EdgeScalar.result_good N mid midGood i hi
  obtain ⟨c1,v,e1,b1,clear,good,width1,f1⟩:=ResetExcept.executes SchurRow.bank EdgeScalar.saved
    (EdgeScalar.patch N mid p) (eraseWidth N B P) C (by unfold eraseWidth;omega)
    rawWidth keepWidth keepGood input tape u patched
  rw [values] at clear good width1
  have source0 : Cells BasisForcing.bank (BasisScalarReload.values p) s.val :=
    fun i hi=>Cells.of_ready state.ready.parts i (Finset.mem_union_left _ hi)
  have source1 : Cells BasisForcing.bank (BasisScalarReload.values p) u.val := source0.transfer_tapes (by
    intro k hk
    obtain ⟨i,hi,cell⟩:=Finset.mem_biUnion.mp hk
    apply EdgeScalar.raw_retained f0 i ?_ k cell
    have low : i<232 := by simpa only [BasisForcing.bank,Finset.mem_range] using hi
    simp only [EdgeScalar.saved,Finset.mem_insert,Finset.mem_singleton]
    omega)
  have source2:=source1.frame f1 source_separate
  have scalarLow (k : ℕ) (lo : 4≤k) (hi : k<900) : u.val.tapes k=s.val.tapes k := by
    apply f0.tapes
    intro member
    have := EdgeScalar.work_range k member
    omega
  have before (k : ℕ) (low : 4≤k) (high : k<600)
      (outside : k∉workspace BasisScalarReload.bank) : v.val.tapes k=s.val.tapes k :=
    (f1.tapes k (fun member=>outside (erased_workspace member))).trans (scalarLow k low (by omega))
  have cleaned : WordCleanup.Bounded BasisReentry.cleanupWords 0 v.val := by
    intro k hk
    have range:=BasisReentry.cleanup_bounds k hk
    refine ⟨[],le_rfl,?_⟩
    apply (RationalAccumulator.zero_word_iff_blank _ _).mpr
    exact RationalAccumulator.blank_of_eq
      (before k (by omega) range.2.1 (BasisReentry.cleanup_workspace k hk)) (state.ready.cleared k hk)
  have reserved (k : ℕ) (hk : k=311 ∨ k=376 ∨ (5≤k ∧ k≤9)) : v.val.tapes k=s.val.tapes k :=
    before k (by omega) (by omega) (reserved_workspace k (by omega))
  have scratch : BankArray.Scratch v.val :=
    ⟨clear.2 0 (by decide),clear.2 1 (by decide),clear.2 2 (by decide),clear.2 3 (by decide),
      RationalAccumulator.blank_of_eq (reserved 5 (by omega)) state.ready.scratch.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (reserved 6 (by omega)) state.ready.scratch.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (reserved 8 (by omega)) state.ready.scratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (reserved 9 (by omega)) state.ready.scratch.2.2.2.2.2.2.2⟩
  have rad : RationalAccumulator.Word v.val 311 R := by
    apply RationalAccumulator.word_of_eq (reserved 311 (by omega))
    simpa only [BasisReentry.radius] using state.ready.naturals 311 (Finset.mem_union_left _ (BasisForcing.naturalIds_decode (by decide)))
  have heapWord : RationalAccumulator.Word v.val 376 heap := by
    apply RationalAccumulator.word_of_eq (reserved 376 (by omega))
    simpa only [BasisReentry.heap] using state.ready.naturals 376 (Finset.mem_union_right _ (by simp))
  obtain ⟨c2,t,e2,b2,canonical,valid,width2,f2⟩:=BasisReentry.executes R heap 0 (max 1 P) (max 1 C)
    (BasisScalarReload.values p) (EdgeScalar.result N mid) (le_max_left _ _)
    (fun i hi=>(state.width i (Finset.mem_union_left _ hi)).mono (le_max_right _ _))
    width1 good input tape v cleaned source2 clear rad heapWord scratch
    (RationalAccumulator.blank_of_eq (reserved 7 (by omega)) state.ready.seven)
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),Nat.add_le_add b0 (Nat.add_le_add b1 b2),
    ⟨canonical,valid,width2⟩,?_,?_,?_⟩
  · intro k lo hi
    apply RationalAccumulator.blank_of_eq ?_ (fresh0 k lo hi)
    exact (f2.tapes k (BasisReentry.changed_middle k (by omega) (by omega))).trans
      (f1.tapes k (fun member=>reserved_workspace k (by omega) (erased_workspace member)))
  · intro k lo hi
    exact (f2.tapes k (BasisReentry.changed_middle k lo (by omega))).trans
      ((f1.tapes k (fun member=>reserved_workspace k (by omega) (erased_workspace member))).trans
        (scalarLow k (by omega) hi))
  · intro k high
    apply (f2.tapes k ?_).trans ((f1.tapes k ?_).trans (f0.tapes k ?_))
    · intro member
      have := BasisReentry.changed_bound k member
      omega
    · intro member
      have := BasisReentry.changed_bound k (Finset.mem_union_right _ (erased_workspace member))
      omega
    · intro member
      have := EdgeScalar.work_range k member
      omega

#print axioms executes
end Maxwell.Continuum.Calibration.EdgeScalarRestart
