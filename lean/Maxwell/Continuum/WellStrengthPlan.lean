import Maxwell.Continuum.WellStrengthOriginalData
import Maxwell.Continuum.RationalDataflowBankWidth
import Maxwell.Continuum.WellOriginalPassData

/-! A physical plan uses the retained raw calibration parts and the exact
source arrays. Its finite width is explicit; polynomial estimates are a
separate resource obligation. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters.WellStrengthPhysical
open Maxwell.Cost Maxwell.Composition Maxwell.Logical Maxwell.Logical.Routing
open RationalDataflow SourceDecorationEnumeration
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
variable (data : CalibratedParts p S hm)

def retainedWidth : ℕ := max 1 (bankWidth WellStrengthReset.parameters (values p S hm data))

theorem retained_width : WidthBank WellStrength.bank (retainedWidth p S hm data) (values p S hm data) := by
  rw [←canonical p S hm data]
  apply WellStrengthReset.canonical_width _ _ (le_max_left _ _)
  intro i hi
  exact (widthBank_bankWidth WellStrengthReset.parameters (values p S hm data) i hi).mono (le_max_right _ _)

def minimumBudget : ℕ := retainedWidth p S hm data+(2^wellStoredPrecision p S hm).bits.length+
  (SourceGraph.Positive.base S (precision p S hm)).bits.length+
  (4*SourceGraph.Positive.count S (precision p S hm)*(SourceGraph.Positive.width S (precision p S hm)+3)).bits.length+
  ((sourceCircuit S (precision p S hm)).size+(sourceCircuit S (precision p S hm)).size+
    (sourceSquareEntries S (precision p S hm)).length).bits.length+4

def plan (hb : S.source≠0) (saved : SourceEmission.Geometry
    ((sourceCircuit S (precision p S hm)).size+(sourceCircuit S (precision p S hm)).size+
      (sourceSquareEntries S (precision p S hm)).length)
    ((sourceSquareEntries S (precision p S hm)).length+(sourceSquareEntries S (precision p S hm)).length))
    (B M boundary : ℕ) (hB : minimumBudget p S hm data ≤ B) (hM : (siteCount saved).bits.length ≤ M)
    (hdiag : SourceGraph.Positive.base S (precision p S hm)+saved.original.size*4 ≤ boundary)
    (hdegree : 4*SourceGraph.Positive.count S (precision p S hm)*(SourceGraph.Positive.width S (precision p S hm)+3)+
      saved.original.size*2 ≤ boundary) : WellOriginalPass.Plan saved.original.size (siteCount saved) := by
  have capacity : saved.original.size ≤ siteCount saved := by unfold siteCount; simp only [Vector.size];omega
  have countbits : saved.original.size.bits.length ≤ (siteCount saved).bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size capacity
  have widths := retained_width p S hm data
  unfold minimumBudget at hB
  exact {
    diagonalWords := diagonalWords p S hm
    degreeWords := degreeWords p S hm
    diagonalBase := SourceGraph.Positive.base S (precision p S hm)
    degreeBase := 4*SourceGraph.Positive.count S (precision p S hm)*(SourceGraph.Positive.width S (precision p S hm)+3)
    precision := wellStoredPrecision p S hm
    budget := B
    metadataBudget := M
    prefixLimit := boundary
    values := values p S hm data
    canonical := canonical p S hm data
    width := fun i hi=>(widths i hi).mono (by omega)
    good := good p S hm data
    budget_ge := by omega
    power_width := by omega
    diagonalBase_width := by omega
    degreeBase_width := by omega
    count_width := by simpa only [Vector.size] using (show
      ((sourceCircuit S (precision p S hm)).size+(sourceCircuit S (precision p S hm)).size+
        (sourceSquareEntries S (precision p S hm)).length).bits.length ≤ B by omega)
    outputIndex_width := countbits.trans hM
    capacity := capacity
    diagonal_below := hdiag
    degree_below := hdegree
    scale_nonzero := scale_nonzero p S hm data
    denominator_nonzero := original_denominator p S hm data hb
  }

#print axioms retained_width
#print axioms plan
end Maxwell.Continuum.RealizationParameters.WellStrengthPhysical
