import Maxwell.Continuum.CalibrationBasisForcingPrepare
import Maxwell.Continuum.CalibrationSchurRow
import Maxwell.Continuum.RationalDataflowRetainedReset
import Maxwell.Continuum.RationalDataflowPartsCopyList
import Maxwell.Continuum.RationalDataflowBankInclusions

/-! Between basis columns, erase the actual old source bank and reload the
five saved physical scalars. Computed Schur entries remain in their cells. -/
namespace Maxwell.Continuum.Calibration.BasisScalarReload
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def bank : Finset ℕ := BasisForcing.bank∪SchurRow.bank
def copies : List (ℕ×ℕ) := [(232,0),(233,1),(234,16),(235,17),(236,18)]
def initial (v : ℕ→Parts) (i : ℕ) : Parts :=
  if i∈BasisForcing.bank then Initialize.parts i else v i
def values (v : ℕ→Parts) : ℕ→Parts := PartsCopies.values copies (initial v)
def code : Code := .seq (Initialize.code BasisForcing.bank) (PartsCopies.code copies)
def costBound (B P : ℕ) : ℕ := Initialize.resetCost BasisForcing.bank B+5*stageCost (max 1 P)+1

attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount

theorem separated : Disjoint BasisForcing.bank SchurRow.bank := by
  apply Finset.disjoint_left.mpr
  intro i source schur
  have low : i < 232 := by simpa only [BasisForcing.bank,Finset.mem_range] using source
  simp only [SchurRow.bank,Finset.mem_union,Finset.mem_Ico] at schur
  omega

theorem copies_valid : ∀p∈copies,p.1∈bank ∧ p.2∈bank ∧ p.1≠p.2 := by
  intro p hp
  simp only [copies,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl
  all_goals
    refine ⟨Finset.mem_union_right _ ?_,Finset.mem_union_left _ ?_,by decide⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by decide))
    · unfold BasisForcing.bank
      decide

theorem source_values (v : ℕ→Parts) :
    values v 0=v 232 ∧ values v 1=v 233 ∧
      values v 16=v 234 ∧ values v 17=v 235 ∧ values v 18=v 236 := by
  simp [values,copies,PartsCopies.values,initial,BasisForcing.bank]

theorem schur_values (v : ℕ→Parts) (i : ℕ) (hi : i∈SchurRow.bank) : values v i=v i := by
  have outside : i∉BasisForcing.bank := fun h=>Finset.disjoint_left.mp separated h hi
  have low : 232 ≤ i := by
    simp only [SchurRow.bank,Finset.mem_union,Finset.mem_Ico] at hi
    omega
  rw [values,PartsCopies.keep]
  · simp only [initial,ite_eq_right outside]
  · intro p hp
    simp only [copies,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl <;> simp only <;> omega

theorem executes (old p : ℕ→Parts) (B P : ℕ) (positive : 1 ≤ B)
    (oldWidth : WidthBank BasisForcing.bank B old) (pwidth : WidthBank SchurRow.bank P p)
    (pgood : Good SchurRow.bank p) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (oldCells : Cells BasisForcing.bank old s.val) (ready : Ready SchurRow.bank p s) :
    ∃cost t,Executes input tape code cost s t ∧ cost ≤ costBound B P ∧
      Ready bank (values p) t ∧ Good bank (values p) ∧ WidthBank bank (max 1 P) (values p) ∧
      BinaryPrecision.Frame (workspace bank) s.val t.val := by
  obtain ⟨c0,u,e0,b0,clear,retained,frame0⟩:=Cells.reset_disjoint_executes
    BasisForcing.bank SchurRow.bank old p B separated positive oldWidth input tape s oldCells ready
  have cells : Cells bank (initial p) u.val := by
    intro i hi
    rcases Finset.mem_union.mp hi with source | schur
    · simpa only [initial,ite_eq_left source] using Cells.of_ready clear i source
    · have outside : i∉BasisForcing.bank := fun h=>Finset.disjoint_left.mp separated h schur
      simpa only [initial,ite_eq_right outside] using Cells.of_ready retained i schur
  have initialWidth : WidthBank bank (max 1 P) (initial p) := by
    intro i hi
    by_cases source : i∈BasisForcing.bank
    · simpa only [initial,ite_eq_left source] using (Initialize.width _ i source).mono (le_max_left _ _)
    · have schur : i∈SchurRow.bank := (Finset.mem_union.mp hi).resolve_left source
      simpa only [initial,ite_eq_right source] using (pwidth i schur).mono (le_max_right _ _)
  have initialGood : Good bank (initial p) := by
    intro i hi
    by_cases source : i∈BasisForcing.bank
    · simpa only [initial,ite_eq_left source] using Initialize.good _ i source
    · have schur : i∈SchurRow.bank := (Finset.mem_union.mp hi).resolve_left source
      simpa only [initial,ite_eq_right source] using pgood i schur
  obtain ⟨c1,t,e1,b1,output,width,frame1⟩:=PartsCopies.executes copies bank copies_valid
    (initial p) (max 1 P) initialWidth input tape u (cells.ready_with clear)
  refine ⟨c0+c1,t,e0.seq e1,?_,output,
    PartsCopies.good copies bank (fun q hq=>(copies_valid q hq).1) (initial p) initialGood,width,
    (frame0.mono ?_).trans frame1⟩
  · simpa only [costBound,copies,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_assoc] using Nat.add_le_add b0 b1
  · intro k hk
    rcases Finset.mem_union.mp hk with scratch | raw
    · exact Finset.mem_union_left _ scratch
    · exact Finset.mem_union_right _ (ids_mono (Finset.subset_union_left) raw)

#print axioms executes
end Maxwell.Continuum.Calibration.BasisScalarReload
