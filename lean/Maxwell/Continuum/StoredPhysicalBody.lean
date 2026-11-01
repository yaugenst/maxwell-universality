import Maxwell.Continuum.WellStrengthSuffixRetention
import Maxwell.Continuum.StoredDescriptionSuffix

/-! Complete charged allocation, physical strength production, well output,
source output, readout output, and finite-decoder suffix. Its caller supplies
the actual source/geometry/calibration words, not a table or execution trace. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical
open RationalDataflow RealizationParameters SourceDecorationEnumeration
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision

def physicalBodyCode : Code:=.seq wellsCode suffixCode
def physicalBodyBits (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz) : List Bool:=
  chronologicalWellStream p S hm++suffixBits p S hm

def physicalBodyCost (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (data : WellStrengthPhysical.CalibratedParts p S hm) (v nv : ℕ→ℕ)
    {V J : ℕ} (q : WellOriginalPass.Plan V J)
    (B H clockLength indexOldWidth oneOldWidth pathCount packedCount : ℕ) : ℕ:=
  costBound v B H clockLength+
    (WellStrengthPass.costBound q 0 0 pathCount packedCount+
      (105*(Table.metadataBudget (Geometry.values v)+H+1)+6*(indexOldWidth+oneOldWidth)+138))+
    WellOutput.costBound (geometryBudget v) (Table.metadataBudget (Geometry.values v)+H+1)
      V pathCount packedCount (Profile.profileBits (materialPrecision p S)) (selectedTemplateBits p S hm)+
    suffixCost p S hm data v nv (Table.metadataBudget (Geometry.values v)+H+1) (H+geometryBudget v) J

theorem wellsCode_positions : wellsCode.protectsInputPositions=true:=by
  simp only [wellsCode,fullCode,code,Geometry.code,Code.protectsInputPositions,WordCleanup.code_inputPositions]
  decide +kernel

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
variable {data : WellStrengthPhysical.CalibratedParts p S hm} {v nv : ℕ→ℕ}

theorem physicalBody_executes {saved} (physical : PhysicalValues p S hm data v saved)
    (hp : Source.Promises p S) (hb : S.source≠0)
    (geometry : Represents S (RealizationParameters.precision p S hm) saved)
    (length_eq : v 2221=length p S hm) (spacing_eq : v 2227=spacing p S hm)
    (buffer_eq : v 2244=bufferSteps p S hm)
    (dimension : nv 500=S.n) (integerBits : nv 4701=(gridReportFormat p S hm).integerBits)
    (fractionalBits : nv 4702=(gridReportFormat p S hm).fractionalBits)
    (sampleCount : nv 4703=gridCount p S hm)
    (side1 : nv 4705=gridSide p S hm 1) (side2 : nv 4706=gridSide p S hm 2)
    (normalization : (nv 4707:ℚ)/(nv 4708)=normalizationScale S)
    (boundary : ℕ)
    (hdiag : SourceGraph.Positive.base S (RealizationParameters.precision p S hm)+saved.original.size*4≤boundary)
    (hdegree : 4*SourceGraph.Positive.count S (RealizationParameters.precision p S hm)*
      (SourceGraph.Positive.width S (RealizationParameters.precision p S hm)+3)+saved.original.size*2≤boundary)
    (habove : boundary≤v 2600) (harray : v 1252+packedLength saved*v 1250≤boundary)
    {B H : ℕ} {clock : List Bool} (hlen : clock.length=v 1250) {s : Store}
    (h : StoredInputs v (WellStrengthPhysical.values p S hm data) B H clock s)
    (source : SourceStrengthTables.Represents S (RealizationParameters.precision p S hm) s.val.memory)
    (stored : StoredGeometry saved (v 1252) (v 1250) s.val.memory)
    (suffix : SuffixInputWords p S hm nv H s)
    (old : ℕ→List Bool) (oldWidth : ∀i∈PartArray.inputHeaderIds,(old i).length≤H)
    (headers : ∀i∈PartArray.inputHeaderIds,BankArray.Word s.val i (old i))
    (indexOld oneOld : List Bool)
    (index : BankArray.Word s.val 728 indexOld) (one : BankArray.Word s.val 727 oneOld)
    (profileWord : BankArray.Word s.val 991 (Profile.profileBits (materialPrecision p S)))
    (templateWord : BankArray.Word s.val 992 (selectedTemplateBits p S hm))
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape physicalBodyCode cost s t ∧
      cost≤physicalBodyCost p S hm data v nv (physicalPlan physical hb boundary hdiag hdegree)
        B H clock.length indexOld.length oneOld.length saved.paths.size (packedLength saved) ∧
      t.val.output=(physicalBodyBits p S hm).reverse++s.val.output ∧
      (∀k,k<boundary→t.val.memory k=s.val.memory k) ∧
      t.val.inputHead=s.val.inputHead ∧t.val.randomCursor=s.val.randomCursor:=by
  obtain ⟨c0,a,table,gv,rv,e0,hc0,out0,ga,_,payload,correct,memory,metadata,counters,raw,clean,power⟩:=
    wells_executes physical hb geometry length_eq spacing_eq buffer_eq boundary hdiag hdegree habove harray
      hlen h source stored old oldWidth headers indexOld oneOld index one profileWord templateWord input tape
  have suffixA:=wells_suffix_stored e0 suffix ga payload raw clean power counters
  have storedA : StoredGeometry saved (v 1252) (v 1250) a.val.memory:=
    ⟨stored.positive,stored.fits,ga.array⟩
  obtain ⟨c1,t,e1,hc1,out1,f1⟩:=suffix_executes physical hp hb geometry length_eq spacing_eq buffer_eq
    dimension integerBits fractionalBits sampleCount side1 side2 normalization hlen storedA table correct
    (Table.metadataBudget (Geometry.values v)+H+1) (H+geometryBudget v) metadata suffixA input tape
  have positions:=e0.protectsInputPositions wellsCode_positions
  refine ⟨c0+c1,t,e0.seq e1,?_,?_,?_,f1.inputHead.trans positions.1,f1.randomCursor.trans positions.2⟩
  · unfold physicalBodyCost
    omega
  · rw [out1,out0]
    simp only [physicalBodyBits,List.reverse_append,List.append_assoc]
  · intro k hk
    rw [f1.memory]
    exact memory k hk

#print axioms physicalBody_executes
end Maxwell.Continuum.WellStrengthInitialization
