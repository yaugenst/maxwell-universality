import Maxwell.Continuum.CalibrationEdgeScalarResultWidth
import Maxwell.Continuum.CalibrationBasisColumnFrame
import Maxwell.Continuum.RationalDataflowBankPartition

/-! Insert the actually produced edge scalars into the retained Schur bank.
Only their five cells change; source cells and canonical headers stay stored. -/
namespace Maxwell.Continuum.Calibration.EdgeScalar
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount

def patch (N : ℕ) (mid : Parts) (p : ℕ→Parts) (i : ℕ) : Parts :=
  if i∈saved then result N mid i else p i

theorem saved_subset : saved⊆SchurRow.bank := by
  intro i hi
  have low : 232≤ i ∧ i<384 := by simp only [saved,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_Ico.mpr low))

theorem raw_retained {s t : Store} (frame : BinaryPrecision.Frame work s.val t.val)
    (i : ℕ) (outside : i∉saved) (k : ℕ) (cell : k∈cellPorts i) : t.val.tapes k=s.val.tapes k := by
  apply frame.tapes
  intro member
  have range:=work_range k member
  simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,Finset.mem_singleton] at cell
  have scalar : i=232 ∨ i=233 ∨ i=234 ∨ i=235 ∨ i=236 := by omega
  apply outside
  simpa only [saved,Finset.mem_insert,Finset.mem_singleton] using scalar

theorem work_retained {s t : Store} (frame : BinaryPrecision.Frame work s.val t.val)
    (k : ℕ) (member : k∈workPorts) : t.val.tapes k=s.val.tapes k := by
  apply frame.tapes
  intro changed
  have range:=work_range k changed
  simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton] at member
  omega

theorem patched_ready {R heap P N : ℕ} {p : ℕ→Parts} {mid : Parts} {s t : Store}
    (state : BasisColumn.State R heap P p s) (stored : Cells saved (result N mid) t.val)
    (scratch : NatAssign.Scratch t.val) (frame : BinaryPrecision.Frame work s.val t.val) :
    Ready SchurRow.bank (patch N mid p) t := by
  have small : Ready saved (result N mid) t := stored.ready (by
    intro k hk
    apply RationalAccumulator.blank_of_eq (work_retained frame k hk)
    have word:=state.ready.parts.1 k (Finset.mem_union_right _ hk)
    have low : k<1000 := by
      simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hk
      omega
    simpa only [dataValues_small _ low,RationalAccumulator.zero_word_iff_blank] using word) scratch
  exact small.partition (state.schur_cells.ready_with state.ready.parts)
    (fun i _ outside k cell=>raw_retained frame i outside k cell)

theorem patch_good (N : ℕ) (mid : Parts) (p : ℕ→Parts) (positive : 0<mid.denominator)
    (good : Good SchurRow.bank p) : Good SchurRow.bank (patch N mid p) := by
  intro i hi
  by_cases scalar : i∈saved
  · simpa only [patch,ite_eq_left scalar] using result_good N mid positive i scalar
  · simpa only [patch,ite_eq_right scalar] using good i hi

theorem patch_width (N B P : ℕ) (mid : Parts) (p : ℕ→Parts) (positive : 1≤B)
    (midWidth : mid.Width B) (oldWidth : WidthBank SchurRow.bank P p) :
    WidthBank SchurRow.bank (max P (resultWidth N B)) (patch N mid p) := by
  intro i hi
  by_cases scalar : i∈saved
  · simpa only [patch,ite_eq_left scalar] using
      (result_width N B mid positive midWidth i scalar).mono (le_max_right _ _)
  · simpa only [patch,ite_eq_right scalar] using (oldWidth i hi).mono (le_max_left _ _)

#print axioms patched_ready
end Maxwell.Continuum.Calibration.EdgeScalar
