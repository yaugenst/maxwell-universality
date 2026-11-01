import Maxwell.Continuum.WellStrengthInitializedPhysical
import Maxwell.Continuum.WellStrengthProducerProtection

/-! The initialized table is filled by the complete proved chronological
producer. The raw-input metadata and exact stored geometry are the only
representation boundary; the strength state is derived internally. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical Maxwell.Logical.Routing
open RationalDataflow RealizationParameters SourceDecorationEnumeration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
variable {data : WellStrengthPhysical.CalibratedParts p S hm} {v : ℕ→ℕ}

def physicalPlan {saved} (physical : PhysicalValues p S hm data v saved) (hb : S.source≠0)
    (boundary : ℕ)
    (hdiag : SourceGraph.Positive.base S (RealizationParameters.precision p S hm)+saved.original.size*4≤boundary)
    (hdegree : 4*SourceGraph.Positive.count S (RealizationParameters.precision p S hm)*(SourceGraph.Positive.width S (RealizationParameters.precision p S hm)+3)+
      saved.original.size*2≤boundary) : WellOriginalPass.Plan saved.original.size (siteCount saved):=
  WellStrengthPhysical.plan p S hm data hb saved (Table.budget (Geometry.values v))
    (Table.metadataBudget (Geometry.values v)) boundary physical.budget physical.metadata hdiag hdegree

theorem Result.produce {saved} (physical : PhysicalValues p S hm data v saved)
    (hb : S.source≠0) (geometry : Represents S (RealizationParameters.precision p S hm) saved)
    (boundary : ℕ)
    (hdiag : SourceGraph.Positive.base S (RealizationParameters.precision p S hm)+saved.original.size*4≤boundary)
    (hdegree : 4*SourceGraph.Positive.count S (RealizationParameters.precision p S hm)*(SourceGraph.Positive.width S (RealizationParameters.precision p S hm)+3)+
      saved.original.size*2≤boundary)
    (habove : boundary≤v 2600)
    (harray : v 1252+packedLength saved*v 1250≤boundary)
    {clock : List Bool} (hlen : clock.length=v 1250) {s : Store}
    (h : Result v (WellStrengthPhysical.values p S hm data) clock s.val.memory s)
    (source : SourceStrengthTables.Represents S (RealizationParameters.precision p S hm) s.val.memory)
    (stored : StoredGeometry saved (v 1252) (v 1250) s.val.memory)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,∃a:PartArray.Table (siteCount saved),∃gv,
      Executes input tape WellStrengthPass.code cost s t ∧
      cost≤WellStrengthPass.costBound (physicalPlan physical hb boundary hdiag hdegree)
        0 0 saved.paths.size (packedLength saved) ∧
      GeometryOutput.Context (packedVector saved) (v 1252) (v 1250) (Table.budget (Geometry.values v))
        clock (Geometry.values v) gv t ∧ gv 971=packedLength saved ∧
      WellStrengthPass.State a (wellStoredPrecision p S hm) (WellStrengthPhysical.values p S hm data) (siteCount saved) t ∧
      WellStrengthPass.Configuration a (wellStoredPrecision p S hm) (Table.budget (Geometry.values v))
        (Table.metadataBudget (Geometry.values v)) boundary ∧
      (∀i:Fin (siteCount saved),a.get i=Parts.literal (wellNumerators p S hm i.val:ℚ)) ∧
      (∀k,k<boundary→t.val.memory k=s.val.memory k) ∧ Blank t.val 972 ∧ Blank t.val 973 ∧
      Word t.val 988 (siteCount saved):=by
  have widths : v 1250≤Table.budget (Geometry.values v):=by
    have hw:=Table.geometry_width (Geometry.values v)
    simpa only [Geometry.values_outside v 1250 (by decide)] using hw
  have packed : (packedLength saved).bits.length≤Table.budget (Geometry.values v):=by
    have hw:=Table.budget_width (Geometry.values v) 1253 (by decide)
    simpa only [Geometry.values_outside v 1253 (by decide),physical.packed] using hw
  exact WellStrengthPhysical.table_executes p S hm data hb geometry
    (Table.budget (Geometry.values v)) (Table.metadataBudget (Geometry.values v)) boundary
    physical.budget physical.metadata hdiag hdegree (h.geometry_context saved stored)
    stored.positive widths hlen packed stored.fits
    (Geometry.output v).1 (Geometry.output v).2.1 (Geometry.output v).2.2.2.2.2.2.2.2.2.1
    ((Geometry.output v).2.2.1.trans physical.original)
    ((Geometry.output v).2.2.2.1.trans physical.edges) (Geometry.output v).2.2.2.2.2.2.2.2.1 harray
    (preparedTable v (siteCount saved) s.val.memory)
    (h.physical_state physical hb boundary hdiag hdegree habove source (fun _ _=>rfl))
    [] [] ((RationalAccumulator.zero_word_iff_blank _ _).mpr h.outer)
    ((RationalAccumulator.zero_word_iff_blank _ _).mpr h.inner) (by simp) input tape

#print axioms Result.produce
end Maxwell.Continuum.WellStrengthInitialization
