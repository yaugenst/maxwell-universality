import Maxwell.Continuum.CalibrationBasisReentryData
import Maxwell.Continuum.RationalDataflowBankTransfer

/-! Charged restart from the actual aftermath of a Schur column. Every old
header and counter is scanned before the source bank and its inputs are reset. -/
namespace Maxwell.Continuum.Calibration.BasisReentry
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount

def code : Code := .seq (WordCleanup.code cleanupWords) BasisScalarReload.code
def changed : Finset ℕ := cleanupWords.toFinset∪workspace BasisScalarReload.bank
def costBound (M B P : ℕ) : ℕ := cleanupWords.length*(6*M+4)+1+BasisScalarReload.costBound B P

theorem changed_bound (k : ℕ) (member : k∈changed) : k<6000 := by
  rcases Finset.mem_union.mp member with cleanup | arithmetic
  · exact ((cleanup_bounds k (List.mem_toFinset.mp cleanup)).2.1).trans (by decide)
  · have banks : ∀i∈BasisScalarReload.bank,i<1371 := by
      intro i hi
      rcases Finset.mem_union.mp hi with source | schur
      · have bound : i<232 := by simpa only [BasisForcing.bank,Finset.mem_range] using source
        omega
      · simp only [SchurRow.bank,SchurRow.nodeCount_value,Finset.mem_union,Finset.mem_Ico] at schur
        omega
    exact (workspace_bound BasisScalarReload.bank 1371 banks k arithmetic).trans (by decide)

private theorem small_outside (k : ℕ) (low : 4≤k) (high : k<1000)
    (gap : k<100 ∨ 106<k) (magnitude : k<30 ∨36<k) : k∉workspace BasisScalarReload.bank := by
  simp only [workspace,ids,Finset.mem_union,not_or]
  refine ⟨by simp only [Finset.mem_insert,Finset.mem_singleton];omega,?_,?_⟩
  · intro h
    obtain ⟨i,_,cell⟩:=Finset.mem_biUnion.mp h
    simp only [cellPorts,positivePort,negativePort,denominatorPort,
      Finset.mem_insert,Finset.mem_singleton] at cell
    omega
  · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton]
    omega

theorem changed_middle (k : ℕ) (low : 600≤k) (high : k<1000) : k∉changed := by
  intro member
  rcases Finset.mem_union.mp member with cleanup | arithmetic
  · have := (cleanup_bounds k (List.mem_toFinset.mp cleanup)).2.1
    omega
  · exact small_outside k (by omega) high (by omega) (by omega) arithmetic

theorem executes (R heap M B P : ℕ) (old p : ℕ→Parts) (positive : 1≤B)
    (oldWidth : WidthBank BasisForcing.bank B old) (pwidth : WidthBank SchurRow.bank P p)
    (pgood : Good SchurRow.bank p) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bounded : WordCleanup.Bounded cleanupWords M s.val)
    (oldCells : Cells BasisForcing.bank old s.val) (ready : Ready SchurRow.bank p s)
    (rad : RationalAccumulator.Word s.val 311 R)
    (free : RationalAccumulator.Word s.val 376 heap)
    (scratch : BankArray.Scratch s.val) (seven : RationalAccumulator.Blank s.val 7) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound M B P ∧
      InputReady R heap p t ∧ Good BasisScalarReload.bank (BasisScalarReload.values p) ∧
      WidthBank BasisScalarReload.bank (max 1 P) (BasisScalarReload.values p) ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,b0,cleared,f0⟩:=WordCleanup.executes cleanupWords M input tape s bounded
  have cells : Cells BasisForcing.bank old u.val := oldCells.transfer (by
    intro k hk
    apply f0.tapes
    simp only [List.mem_toFinset]
    intro erased
    have := (cleanup_bounds k erased).2.1
    omega)
  have schur : Ready SchurRow.bank p u := ready.transfer_tapes (by
    intro k hk
    apply f0.tapes
    simp only [List.mem_toFinset]
    intro erased
    apply cleanup_workspace k erased
    rcases Finset.mem_union.mp hk with small | raw
    · exact Finset.mem_union_left _ small
    · exact Finset.mem_union_right _ (ids_mono Finset.subset_union_right raw))
  obtain ⟨c1,t,e1,b1,output,good,width,f1⟩:=BasisScalarReload.executes
    old p B P positive oldWidth pwidth pgood input tape u cells schur
  have keep (k : ℕ) (notClear : k∉cleanupWords)
      (notBank : k∉workspace BasisScalarReload.bank) : t.val.tapes k=s.val.tapes k :=
    (f1.tapes k notBank).trans (f0.tapes k (by simpa only [List.mem_toFinset] using notClear))
  have clean : ∀k∈cleanupWords,RationalAccumulator.Blank t.val k := by
    intro k hk
    exact RationalAccumulator.blank_of_eq (f1.tapes k (cleanup_workspace k hk)) (cleared k hk)
  have reserved (k : ℕ) (hk : k=311 ∨ k=376 ∨ (5≤k ∧ k≤9)) : t.val.tapes k=s.val.tapes k := by
    apply keep
    · intro h
      obtain ⟨low,_,nr,nh⟩:=cleanup_bounds k h
      omega
    · apply small_outside <;> omega
  have outScratch : BankArray.Scratch t.val := by
    refine ⟨output.2 0 (by decide),output.2 1 (by decide),output.2 2 (by decide),
      output.2 3 (by decide),?_,?_,?_,?_⟩
    · exact RationalAccumulator.blank_of_eq (reserved 5 (by omega)) scratch.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (reserved 6 (by omega)) scratch.2.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (reserved 8 (by omega)) scratch.2.2.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (reserved 9 (by omega)) scratch.2.2.2.2.2.2.2
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add b0 b1,
    assemble R heap p t output clean
      (RationalAccumulator.word_of_eq (reserved 311 (by omega)) rad)
      (RationalAccumulator.word_of_eq (reserved 376 (by omega)) free)
      outScratch (RationalAccumulator.blank_of_eq (reserved 7 (by omega)) seven),good,width,
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)⟩

#print axioms executes
end Maxwell.Continuum.Calibration.BasisReentry
