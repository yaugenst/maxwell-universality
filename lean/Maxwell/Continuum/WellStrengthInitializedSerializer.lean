import Maxwell.Continuum.WellStrengthInitializedProducer
import Maxwell.Continuum.WellStrengthSerializerHandoff

/-! Charged handoff from the actually produced chronological strength table
to the well serializer. Its header and profile words are retained through
every producer loop and then used by the fixed descriptor-copy program. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical Maxwell.Logical.Routing
open RationalDataflow RealizationParameters SourceDecorationEnumeration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def produceHandoffCode : Code := .seq WellStrengthPass.code WellStrengthPass.handoffCode

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
variable {data : WellStrengthPhysical.CalibratedParts p S hm} {v : ℕ→ℕ}

theorem Result.produce_serializer {saved} (physical : PhysicalValues p S hm data v saved)
    (hb : S.source≠0) (geometry : Represents S (RealizationParameters.precision p S hm) saved)
    (boundary : ℕ)
    (hdiag : SourceGraph.Positive.base S (RealizationParameters.precision p S hm)+saved.original.size*4≤boundary)
    (hdegree : 4*SourceGraph.Positive.count S (RealizationParameters.precision p S hm)*
      (SourceGraph.Positive.width S (RealizationParameters.precision p S hm)+3)+saved.original.size*2≤boundary)
    (habove : boundary≤v 2600) (harray : v 1252+packedLength saved*v 1250≤boundary)
    {clock : List Bool} (hlen : clock.length=v 1250) {s : Store}
    (h : Result v (WellStrengthPhysical.values p S hm data) clock s.val.memory s)
    (source : SourceStrengthTables.Represents S (RealizationParameters.precision p S hm) s.val.memory)
    (stored : StoredGeometry saved (v 1252) (v 1250) s.val.memory)
    (old : ℕ→List Bool) (H : ℕ) (oldWidth : ∀i∈PartArray.inputHeaderIds,(old i).length≤H)
    (headers : ∀i∈PartArray.inputHeaderIds,BankArray.Word s.val i (old i))
    (indexOld oneOld profile template : List Bool)
    (index : BankArray.Word s.val 728 indexOld) (one : BankArray.Word s.val 727 oneOld)
    (profileWord : BankArray.Word s.val 991 profile) (templateWord : BankArray.Word s.val 992 template)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,∃a:PartArray.Table (siteCount saved),∃gv,
      Executes input tape produceHandoffCode cost s t ∧
      cost≤WellStrengthPass.costBound (physicalPlan physical hb boundary hdiag hdegree) 0 0 saved.paths.size (packedLength saved)+
        (105*(Table.metadataBudget (Geometry.values v)+H+1)+6*(indexOld.length+oneOld.length)+138) ∧
      GeometryOutput.Context (packedVector saved) (v 1252) (v 1250) (Table.budget (Geometry.values v))
        clock (Geometry.values v) gv t ∧ gv 971=packedLength saved ∧
      WellPayload.State a (wellStoredPrecision p S hm) (Table.metadataBudget (Geometry.values v)+H+1)
        0 profile template (WellStrengthPhysical.values p S hm data) t ∧
      (∀i:Fin (siteCount saved),a.get i=Parts.literal (wellNumerators p S hm i.val:ℚ)) ∧
      (∀k,k<boundary→t.val.memory k=s.val.memory k) ∧
      a.MetadataWidth (Table.metadataBudget (Geometry.values v)+H+1) ∧
      Word t.val 988 (siteCount saved) ∧ Blank t.val 972 ∧ Blank t.val 973 ∧
      Ready WellStrength.bank (WellStrengthPhysical.values p S hm data) t ∧
      DyadicFloor.Clean t.val ∧Word t.val 144 (2^wellStoredPrecision p S hm):=by
  obtain ⟨c0,a,table,gv,e0,h0,ga,indexA,sa,config,correct,mem,outerA,innerA,totalA⟩:=
    h.produce physical hb geometry boundary hdiag hdegree habove harray hlen source stored input tape
  have payloadKeep (i : ℕ) (lo : 990≤ i) (hi : i<993) :=
    e0.outsideTapes WellStrengthPass.code_preserves_payload i lo hi
  have cursorKeep (i : ℕ) (lo : 727≤ i) (hi : i<729) :=
    e0.outsideTapes WellStrengthPass.code_preserves_serializer_cursors i lo hi
  have oldA : ∀i∈PartArray.inputHeaderIds,BankArray.Word a.val i (old i):=by
    intro i hi
    have bounds : 200≤ i ∧ i<206:=by
      simp only [PartArray.inputHeaderIds,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact BankArray.word_of_eq (e0.outsideTapes WellStrengthPass.code_preserves_input_headers i bounds.1 bounds.2)
      (headers i hi)
  obtain ⟨c1,t,e1,h1,payload,f1⟩:=WellStrengthPass.handoff_executes table
    (config.metadata.mono (by omega : Table.metadataBudget (Geometry.values v)≤Table.metadataBudget (Geometry.values v)+H+1))
    (WellStrengthPhysical.values p S hm data)
    (WellStrengthPass.canonical_serializer_width _ (WellStrengthPhysical.canonical p S hm data) _ (by omega))
    old (fun i hi=>(oldWidth i hi).trans (by omega)) indexOld oneOld profile template input tape a
    sa.serializer_ready sa.table oldA
    (BankArray.word_of_eq (cursorKeep 728 (by decide) (by decide)) index)
    (BankArray.word_of_eq (cursorKeep 727 (by decide) (by decide)) one)
    (RationalAccumulator.word_of_eq (payloadKeep 990 (by decide) (by decide))
      (by simpa only [physical.precision_eq] using h.precision))
    (BankArray.word_of_eq (payloadKeep 991 (by decide) (by decide)) profileWord)
    (BankArray.word_of_eq (payloadKeep 992 (by decide) (by decide)) templateWord)
  refine ⟨c0+c1,t,table,gv,e0.seq e1,by omega,WellStrengthPass.handoff_geometry_frame ga f1,indexA,payload,correct,?_,config.metadata.mono (by omega),
    RationalAccumulator.word_of_eq (f1.tapes 988 (by decide)) totalA,
    RationalAccumulator.blank_of_eq (f1.tapes 972 (by decide)) outerA,
    RationalAccumulator.blank_of_eq (f1.tapes 973 (by decide)) innerA,
    WellStrengthPass.handoff_rational_frame sa.rational f1,?_,
    RationalAccumulator.word_of_eq (f1.tapes 144 (by decide)) sa.power⟩
  · intro k hk
    rw [f1.memory]
    exact mem k hk
  · refine ⟨RationalAccumulator.blank_of_eq (f1.tapes 4 (by decide)) sa.clean.1,?_⟩
    intro i hi
    exact RationalAccumulator.blank_of_eq (f1.tapes i (fun hh=>Finset.disjoint_left.mp
      (by decide : Disjoint (DyadicFloor.extraIds∪NaturalQuotient.workPorts) WellStrengthPass.handoffIds) hi hh)) (sa.clean.2 i hi)

#print axioms Result.produce_serializer
end Maxwell.Continuum.WellStrengthInitialization
