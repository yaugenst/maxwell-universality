import Maxwell.Continuum.StoredAmbientRetention

/-! The actual ambient cube stream precedes the physical body. This fixed
program preserves the original source archive while allocating and emitting
the complete well/source/readout/decoder payload. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical
open RationalDataflow RealizationParameters SourceDecorationEnumeration
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision

def ambientBodyCode : Code:=.seq StoredAmbient.relocatedCode physicalBodyCode

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
variable {data : WellStrengthPhysical.CalibratedParts p S hm} {v nv : ℕ→ℕ}

theorem ambientBody_executes {saved} (physical : PhysicalValues p S hm data v saved)
    (hp : Source.Promises p S) (hb : S.source≠0)
    (geometry : Represents S (RealizationParameters.precision p S hm) saved)
    (selected : DecoderSelectors.Inputs p S hm v) (spacing_eq : v 2227=spacing p S hm)
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
    (A AH : ℕ) (hA : 3≤A)
    (ambientWidth : ∀i∈StoredAmbient.inputs,(v i).bits.length≤A)
    (ambientBank : NatAssign.Bank StoredAmbient.inputs v s.val)
    (ambientOld : WordCleanup.Bounded StoredAmbient.relocatedOld AH s.val)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape ambientBodyCode cost s t ∧
      cost≤StoredAmbient.relocatedCost v A AH+physicalBodyCost p S hm data v nv (physicalPlan physical hb boundary hdiag hdegree)
        B H clock.length indexOld.length oneOld.length saved.paths.size (packedLength saved) ∧
      t.val.output=(ambientBits p S hm++physicalBodyBits p S hm).reverse++s.val.output ∧
      (∀k,k<boundary→t.val.memory k=s.val.memory k) ∧
      t.val.inputHead=s.val.inputHead ∧t.val.randomCursor=s.val.randomCursor :=by
  obtain ⟨c0,a,e0,hc0,out0,scratch,frame⟩:=StoredAmbient.physical_executes selected A AH hA
    ambientWidth input tape s ambientBank h.rational.2 ambientOld
  have keep:=ambient_kept frame
  have sourceA : SourceStrengthTables.Represents S (RealizationParameters.precision p S hm) a.val.memory:=by
    simpa only [frame.memory] using source
  have storedA : StoredGeometry saved (v 1252) (v 1250) a.val.memory:=by
    simpa only [frame.memory] using stored
  have headersA : ∀i∈PartArray.inputHeaderIds,BankArray.Word a.val i (old i):=by
    intro i hi
    have bounds : ∀i∈PartArray.inputHeaderIds,4≤ i ∧i<5000:=by decide +kernel
    exact BankArray.word_of_eq (keep i (bounds i hi).1 (bounds i hi).2) (headers i hi)
  obtain ⟨c1,t,e1,hc1,out1,memory,head,random⟩:=physicalBody_executes physical hp hb geometry
    selected.length_eq spacing_eq selected.buffer_eq dimension integerBits fractionalBits sampleCount
    side1 side2 normalization boundary hdiag hdegree habove harray hlen (h.ambient frame scratch)
    sourceA storedA (suffix.ambient frame scratch) old oldWidth headersA indexOld oneOld
    (BankArray.word_of_eq (keep 728 (by decide) (by decide)) index)
    (BankArray.word_of_eq (keep 727 (by decide) (by decide)) one)
    (BankArray.word_of_eq (keep 991 (by decide) (by decide)) profileWord)
    (BankArray.word_of_eq (keep 992 (by decide) (by decide)) templateWord) input tape
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add hc0 hc1,?_,?_,head.trans frame.inputHead,
    random.trans frame.randomCursor⟩
  · rw [out1,out0]
    simp only [List.reverse_append,List.append_assoc]
  · intro k hk
    rw [memory k hk,frame.memory]

#print axioms ambientBody_executes
end Maxwell.Continuum.WellStrengthInitialization
