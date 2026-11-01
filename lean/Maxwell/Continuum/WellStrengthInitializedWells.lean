import Maxwell.Continuum.StoredWellRawFrame
import Maxwell.Continuum.WellStrengthWellSerialization
import Maxwell.Cost.Structured.OutputFootprint

/-! Complete charged allocation, strength production, and exact chronological
well serialization from stored source, geometry, and calibration operands. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical Maxwell.Logical.Routing
open RationalDataflow RealizationParameters SourceDecorationEnumeration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 6500000
set_option maxRecDepth 16384

def wellsCode : Code := .seq fullCode WellOutput.code

theorem fullCode_output : fullCode.protectsOutput=true:=by
  simp only [fullCode,code,Geometry.code,Code.protectsOutput,WordCleanup.code_output,Bool.true_and]
  decide +kernel

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
variable {data : WellStrengthPhysical.CalibratedParts p S hm} {v : ℕ→ℕ}

theorem wells_executes {saved} (physical : PhysicalValues p S hm data v saved)
    (hb : S.source≠0) (geometry : Represents S (RealizationParameters.precision p S hm) saved)
    (length_eq : v 2221=length p S hm) (spacing_eq : v 2227=spacing p S hm)
    (buffer_eq : v 2244=bufferSteps p S hm)
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
    (indexOld oneOld : List Bool)
    (index : BankArray.Word s.val 728 indexOld) (one : BankArray.Word s.val 727 oneOld)
    (profileWord : BankArray.Word s.val 991 (Profile.profileBits (materialPrecision p S))) (templateWord : BankArray.Word s.val 992 (selectedTemplateBits p S hm))
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,∃a:PartArray.Table (siteCount saved),∃gv r,
      Executes input tape wellsCode cost s t ∧
      cost≤costBound v B H clock.length+
        (WellStrengthPass.costBound (physicalPlan physical hb boundary hdiag hdegree) 0 0 saved.paths.size (packedLength saved)+
          (105*(Table.metadataBudget (Geometry.values v)+H+1)+6*(indexOld.length+oneOld.length)+138))+
        WellOutput.costBound (geometryBudget v) (Table.metadataBudget (Geometry.values v)+H+1)
          saved.original.size saved.paths.size (packedLength saved)
          (Profile.profileBits (materialPrecision p S)) (selectedTemplateBits p S hm) ∧
      t.val.output=(chronologicalWellStream p S hm).reverse++s.val.output ∧
      GeometryOutput.Context (packedVector saved) (v 1252) (v 1250) (geometryBudget v)
        clock (Geometry.values v) gv t ∧ gv 971=packedLength saved ∧
      WellPayload.State a (wellStoredPrecision p S hm) (Table.metadataBudget (Geometry.values v)+H+1)
        (siteCount saved) (Profile.profileBits (materialPrecision p S)) (selectedTemplateBits p S hm) r t ∧
      (∀i:Fin (siteCount saved),a.get i=Parts.literal (wellNumerators p S hm i.val:ℚ)) ∧
      (∀k,k<boundary→t.val.memory k=s.val.memory k) ∧
      a.MetadataWidth (Table.metadataBudget (Geometry.values v)+H+1) ∧
      WordCleanup.Bounded [972,973] (geometryBudget v) t.val ∧
      Ready WellStrength.bank (Function.update (WellStrengthPhysical.values p S hm data) 0 (r 0)) t ∧
      DyadicFloor.Clean t.val ∧Word t.val 144 (2^wellStoredPrecision p S hm):=by
  obtain ⟨c0,a,table,gv,e0,h0,g,_,payload,correct,mem,metadata,total,outer,inner,raw,clean,power⟩:=
    full_executes physical hb geometry boundary hdiag hdegree habove harray hlen h source stored
      old oldWidth headers indexOld oneOld (Profile.profileBits (materialPrecision p S))
      (selectedTemplateBits p S hm) index one profileWord templateWord input tape
  have storedA : StoredGeometry saved (v 1252) (v 1250) a.val.memory:=
    ⟨stored.positive,stored.fits,g.array⟩
  obtain ⟨c1,t,w,r,e1,h1,output,memory,gt,ix,pt,controls⟩:=serialize physical geometry length_eq spacing_eq buffer_eq
    hlen g storedA table correct H metadata payload total outer inner input tape
  refine ⟨c0+c1,t,table,w,r,e0.seq e1,by omega,?_,gt,ix,pt,correct,?_,metadata,controls,WellPayload.raw_frame e1 raw pt,WellPayload.rounding_frame e1 clean power⟩
  · rw [output,e0.protectsOutput fullCode_output]
  · intro k hk
    rw [memory]
    exact mem k hk

#print axioms wells_executes
end Maxwell.Continuum.WellStrengthInitialization
