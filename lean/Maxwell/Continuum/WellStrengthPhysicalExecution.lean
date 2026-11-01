import Maxwell.Continuum.WellStrengthPlan
import Maxwell.Continuum.WellStrengthTableProduction

/-! The fixed strength producer fills the actual chronological physical
numerator table. Calibration is consumed as raw represented parts; all
physical target identities and reciprocal side conditions are proved here. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters.WellStrengthPhysical
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open Maxwell.Composition Maxwell.Logical Maxwell.Logical.Routing
open RationalDataflow SourceDecorationEnumeration
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
variable (data : CalibratedParts p S hm)

theorem table_executes (hb : S.source≠0) {saved} (geometry : Represents S (precision p S hm) saved)
    (B M boundary : ℕ) (hB : minimumBudget p S hm data ≤ B) (hM : (siteCount saved).bits.length ≤ M)
    (hdiag : SourceGraph.Positive.base S (precision p S hm)+saved.original.size*4 ≤ boundary)
    (hdegree : 4*SourceGraph.Positive.count S (precision p S hm)*(SourceGraph.Positive.width S (precision p S hm)+3)+
      saved.original.size*2 ≤ boundary)
    {base width initialIndex : ℕ} {clock : List Bool} {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context (packedVector saved) base width B clock constants gv s)
    (hw : 0<width) (hwidth : width ≤ B) (hlen : clock.length=width)
    (hn : (packedLength saved).bits.length ≤ B)
    (hfit : ∀i,((packedVector saved).get i).bits.length ≤ width)
    (hbase : constants 960=base) (hword : constants 961=width) (ho : constants 970=1)
    (hV : constants 963=saved.original.size) (hE : constants 964=saved.paths.size) (hthree : constants 969=3)
    (harray : base+packedLength saved*width ≤ boundary)
    (a : PartArray.Table (siteCount saved))
    (state : WellOriginalPass.State (plan p S hm data hb saved B M boundary hB hM hdiag hdegree)
      a initialIndex s.val.memory s)
    (outer inner : List Bool) (hout : BankArray.Word s.val 972 outer) (hin : BankArray.Word s.val 973 inner)
    (hinner : inner.length ≤ B) (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,∃a':PartArray.Table (siteCount saved),∃gv',
      Executes input tape WellStrengthPass.code cost s t ∧
      cost ≤ WellStrengthPass.costBound (plan p S hm data hb saved B M boundary hB hM hdiag hdegree)
        initialIndex outer.length saved.paths.size (packedLength saved) ∧
      GeometryOutput.Context (packedVector saved) base width B clock constants gv' t ∧
      gv' 971=packedLength saved ∧
      WellStrengthPass.State a' (wellStoredPrecision p S hm) (values p S hm data) (siteCount saved) t ∧
      WellStrengthPass.Configuration a' (wellStoredPrecision p S hm) B M boundary ∧
      (∀i:Fin (siteCount saved),a'.get i=Parts.literal (wellNumerators p S hm i.val:ℚ)) ∧
      (∀k,k<boundary→t.val.memory k=s.val.memory k) ∧
      Blank t.val 972 ∧ Blank t.val 973 ∧ Word t.val 988 (siteCount saved) := by
  let q := plan p S hm data hb saved B M boundary hB hM hdiag hdegree
  apply WellStrengthPass.executes saved q g hw hwidth hlen hn hfit hbase hword ho hV hE hthree
    (packedLength saved) (Represents.path_length_two S (precision p S hm) geometry)
    (fun i=>by have span := pathOffset_span saved i;omega) harray (siteCount_eq_prefix saved).symm hM
    (internal_denominator p S hm data) (mediator_denominator p S hm data geometry hb)
    (fun i=>Parts.literal (wellNumerators p S hm i:ℚ))
    (fun j hj=>original_part p S hm data geometry ⟨j,hj⟩)
    (internal_part p S hm data geometry) (mediator_part p S hm data geometry)
    a state outer inner hout hin hinner input tape

#print axioms table_executes
end Maxwell.Continuum.RealizationParameters.WellStrengthPhysical
