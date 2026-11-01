import Maxwell.Continuum.WellStrengthInitializedState
import Maxwell.Continuum.WellStrengthPhysicalExecution

/-! The semantic physical plan is discharged from computed metadata and raw
calibration channels. No execution or preallocated strength table is supplied. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical Maxwell.Logical.Routing
open RationalDataflow RealizationParameters SourceDecorationEnumeration
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

structure PhysicalValues (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (data : WellStrengthPhysical.CalibratedParts p S hm) (v : ℕ→ℕ)
    (saved : SourceEmission.Geometry
      ((sourceCircuit S (RealizationParameters.precision p S hm)).size+(sourceCircuit S (RealizationParameters.precision p S hm)).size+
        (sourceSquareEntries S (RealizationParameters.precision p S hm)).length)
      ((sourceSquareEntries S (RealizationParameters.precision p S hm)).length+(sourceSquareEntries S (RealizationParameters.precision p S hm)).length)) : Prop where
  parts : ∀i∈Table.parameterSources,v i=dataValues (WellStrengthPhysical.values p S hm data) i
  precision_eq : v 990=wellStoredPrecision p S hm
  power : v 144=2^wellStoredPrecision p S hm
  diagonal : v 145=SourceGraph.Positive.base S (RealizationParameters.precision p S hm)
  degree : v 143=4*SourceGraph.Positive.count S (RealizationParameters.precision p S hm)*(SourceGraph.Positive.width S (RealizationParameters.precision p S hm)+3)
  original : v 141=saved.original.size
  edges : v 153=saved.paths.size
  count : v 1209=siteCount saved
  packed : v 1253=packedLength saved

theorem PhysicalValues.budget {p S hm data v saved} (h : PhysicalValues p S hm data v saved) :
    WellStrengthPhysical.minimumBudget p S hm data≤Table.budget (Geometry.values v):=by
  apply Table.physical_budget p S hm data (Geometry.values v)
  · intro i hi
    rw [Geometry.values_outside v i ?_]
    · exact h.parts i hi
    · have disjoint : Disjoint Table.parameterSources.toFinset Geometry.targets:=by decide
      exact Finset.disjoint_left.mp disjoint (by simpa only [List.mem_toFinset] using hi)
  · rw [Geometry.values_outside v 144 (by decide),h.power]
  · rw [Geometry.values_outside v 145 (by decide),h.diagonal]
  · rw [Geometry.values_outside v 143 (by decide),h.degree]
  · rw [Geometry.values_outside v 141 (by decide),h.original]


theorem PhysicalValues.metadata {p S hm data v saved} (h : PhysicalValues p S hm data v saved) :
    (siteCount saved).bits.length≤Table.metadataBudget (Geometry.values v):=by
  unfold Table.metadataBudget
  rw [Geometry.values_outside v 1209 (by decide),h.count]
  omega

theorem Result.physical_state {p S hm data v saved} (physical : PhysicalValues p S hm data v saved)
    (hb : S.source≠0) (boundary : ℕ)
    (hdiag : SourceGraph.Positive.base S (RealizationParameters.precision p S hm)+saved.original.size*4≤boundary)
    (hdegree : 4*SourceGraph.Positive.count S (RealizationParameters.precision p S hm)*(SourceGraph.Positive.width S (RealizationParameters.precision p S hm)+3)+
      saved.original.size*2≤boundary)
    (habove : boundary≤v 2600) {clock memory s}
    (h : Result v (WellStrengthPhysical.values p S hm data) clock memory s)
    (source : SourceStrengthTables.Represents S (RealizationParameters.precision p S hm) s.val.memory)
    (preserved : ∀j,j<boundary→s.val.memory j=memory j) :
    WellOriginalPass.State
      (WellStrengthPhysical.plan p S hm data hb saved (Table.budget (Geometry.values v))
        (Table.metadataBudget (Geometry.values v)) boundary physical.budget physical.metadata hdiag hdegree)
      (preparedTable v (siteCount saved) memory) 0 memory s:=by
  apply h.original_state physical.precision_eq physical.power rfl rfl physical.count physical.original
    physical.diagonal physical.degree habove
  · exact WellStrengthPhysical.diagonal_represented p S hm source
  · exact WellStrengthPhysical.degree_represented p S hm source
  · exact preserved

#print axioms Result.physical_state
end Maxwell.Continuum.WellStrengthInitialization
