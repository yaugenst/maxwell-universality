import Maxwell.Continuum.WellStrengthInitializedSerializer

/-! One fixed program takes the stored source, geometry, calibration, and
selected-parameter words through measured allocation, full strength production,
and the descriptor handoff to the serializer. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical Maxwell.Logical.Routing
open RationalDataflow RealizationParameters SourceDecorationEnumeration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 6500000
set_option maxRecDepth 16384

structure StoredInputs (v : ℕ→ℕ) (parts : ℕ→Parts) (B H : ℕ) (clock : List Bool) (s : Store) : Prop where
  budget_ge : 54≤B
  width : ∀i∈inputs,(v i).bits.length≤B
  bank : NatAssign.Bank inputs v s.val
  scratch : BankArray.Scratch s.val
  rational : Ready WellStrength.bank parts s
  seven : Blank s.val 7
  thirtySeven : Blank s.val 37
  temp : Blank s.val 216
  clockWord : BankArray.Word s.val 1251 clock
  oldGeometry : WordCleanup.Bounded Geometry.clearHeaders H s.val
  oldTable : WordCleanup.Bounded Table.clearHeaders H s.val
  oldAllocation : WordCleanup.Bounded Table.Allocation.clearHeaders H s.val
  oldClean : WordCleanup.Bounded cleanHeaders H s.val

def fullCode : Code := .seq code produceHandoffCode

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
variable {data : WellStrengthPhysical.CalibratedParts p S hm} {v : ℕ→ℕ}

theorem full_executes {saved} (physical : PhysicalValues p S hm data v saved)
    (hb : S.source≠0) (geometry : Represents S (RealizationParameters.precision p S hm) saved)
    (boundary : ℕ)
    (hdiag : SourceGraph.Positive.base S (RealizationParameters.precision p S hm)+saved.original.size*4≤boundary)
    (hdegree : 4*SourceGraph.Positive.count S (RealizationParameters.precision p S hm)*
      (SourceGraph.Positive.width S (RealizationParameters.precision p S hm)+3)+saved.original.size*2≤boundary)
    (habove : boundary≤v 2600) (harray : v 1252+packedLength saved*v 1250≤boundary)
    {B H : ℕ} {clock : List Bool} (hlen : clock.length=v 1250) {s : Store}
    (h : StoredInputs v (WellStrengthPhysical.values p S hm data) B H clock s)
    (source : SourceStrengthTables.Represents S (RealizationParameters.precision p S hm) s.val.memory)
    (stored : StoredGeometry saved (v 1252) (v 1250) s.val.memory)
    (old : ℕ→List Bool) (oldWidth : ∀i∈PartArray.inputHeaderIds,(old i).length≤H)
    (headers : ∀i∈PartArray.inputHeaderIds,BankArray.Word s.val i (old i))
    (indexOld oneOld profile template : List Bool)
    (index : BankArray.Word s.val 728 indexOld) (one : BankArray.Word s.val 727 oneOld)
    (profileWord : BankArray.Word s.val 991 profile) (templateWord : BankArray.Word s.val 992 template)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,∃a:PartArray.Table (siteCount saved),∃gv,
      Executes input tape fullCode cost s t ∧
      cost≤costBound v B H clock.length+
        (WellStrengthPass.costBound (physicalPlan physical hb boundary hdiag hdegree) 0 0 saved.paths.size (packedLength saved)+
          (105*(Table.metadataBudget (Geometry.values v)+H+1)+6*(indexOld.length+oneOld.length)+138)) ∧
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
  obtain ⟨c0,a,e0,h0,ra,f0⟩:=executes v (WellStrengthPhysical.values p S hm data) B H h.budget_ge h.width
    clock input tape s h.bank h.scratch h.rational h.seven h.thirtySeven h.temp h.clockWord
    h.oldGeometry h.oldTable h.oldAllocation h.oldClean
  have ready : Result v (WellStrengthPhysical.values p S hm data) clock a.val.memory a:=by
    simpa only [f0.memory] using ra
  have sourceA : SourceStrengthTables.Represents S (RealizationParameters.precision p S hm) a.val.memory:=by
    simpa only [f0.memory] using source
  have storedA : StoredGeometry saved (v 1252) (v 1250) a.val.memory:=by simpa only [f0.memory] using stored
  have headersA : ∀i∈PartArray.inputHeaderIds,BankArray.Word a.val i (old i):=by
    intro i hi
    apply BankArray.word_of_eq (f0.tapes i ?_) (headers i hi)
    have disjoint : Disjoint PartArray.inputHeaderIds work:=by decide
    exact Finset.disjoint_left.mp disjoint hi
  obtain ⟨c1,t,table,gv,e1,h1,g,ix,payload,correct,mem,metadata,total,outer,inner,raw,clean,power⟩:=ready.produce_serializer physical hb geometry boundary
    hdiag hdegree habove harray hlen sourceA storedA old H oldWidth headersA indexOld oneOld profile template
    (BankArray.word_of_eq (f0.tapes 728 (by decide)) index)
    (BankArray.word_of_eq (f0.tapes 727 (by decide)) one)
    (BankArray.word_of_eq (f0.tapes 991 (by decide)) profileWord)
    (BankArray.word_of_eq (f0.tapes 992 (by decide)) templateWord) input tape
  refine ⟨c0+c1,t,table,gv,e0.seq e1,by omega,g,ix,payload,correct,?_,metadata,total,outer,inner,raw,clean,power⟩
  intro k hk
  rw [mem k hk,f0.memory]

#print axioms full_executes
end Maxwell.Continuum.WellStrengthInitialization
