import Maxwell.Continuum.StoredSourcePhysicalPlan
import Maxwell.Continuum.StoredSourcePreparedStream

/-! Actual complete source serialization from the post-well raw bank and
retained source archive. All scalar identities and reciprocal conditions
are derived from the physical construction. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical
open RationalDataflow RealizationParameters SourceDecorationEnumeration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision

def sourceInitialWidth (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (data : WellStrengthPhysical.CalibratedParts p S hm) (payloadWidth oldWidth : ℕ) : ℕ:=
  2+WellStrengthPhysical.retainedWidth p S hm data+payloadWidth+oldWidth+MagnitudeMax.inputWidth p S

def sourceCost (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (v : ℕ→ℕ) (B H A C : ℕ) : ℕ:=
  SourcePayload.setupCost (sourcePrecision p S) B H+
    (((6*geometryBudget v+11)+((6*A+15*(LogRats.records (List.ofFn S.source)).length+21)+
      (6*C+15*S.n.bits.length+21)))+(20*S.n.bits.length+24)+
      ((S.n+1)*(13*S.n.bits.length+15)+S.n*(2^30*(geometryBudget v+3)^2+
        (2^200*(sourcePrecision p S+sourceBankWidth p S B+8)^2+10*(selectedTemplateBits p S hm).length))))

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
variable {data : WellStrengthPhysical.CalibratedParts p S hm} {v : ℕ→ℕ}

theorem sources_executes {saved} (physical : PhysicalValues p S hm data v saved)
    (hp : Source.Promises p S) (hb : S.source≠0)
    (geometry : Represents S (RealizationParameters.precision p S hm) saved)
    (length_eq : v 2221=length p S hm) (spacing_eq : v 2227=spacing p S hm)
    (buffer_eq : v 2244=bufferSteps p S hm)
    {clock : List Bool} (hlen : clock.length=v 1250) {s : Store} {gv : ℕ→ℕ}
    (g : GeometryOutput.Context (packedVector saved) (v 1252) (v 1250) (geometryBudget v)
      clock (Geometry.values v) gv s)
    (stored : StoredGeometry saved (v 1252) (v 1250) s.val.memory)
    (last : Parts) (M H : ℕ) (lastWidth : last.Width M)
    (raw : Ready WellStrength.bank (Function.update (WellStrengthPhysical.values p S hm data) 0 last) s)
    (clean : DyadicFloor.Clean s.val)
    (num : Word s.val 506 (NormalizeRatio.sourceScalePair S).1)
    (den : Word s.val 507 (NormalizeRatio.sourceScalePair S).2)
    (precisionWord : Word s.val 4427 (sourcePrecision p S))
    (powerOld : WordCleanup.Bounded [4808,144] H s.val)
    (templateWord : BankArray.Word s.val 992 (selectedTemplateBits p S hm))
    (archive : BankArray.Word s.val 508 (LogRats.records (List.ofFn S.source)))
    (count : Word s.val 500 S.n) (oldArchive oldCount : List Bool)
    (archiveOld : BankArray.Word s.val 85 oldArchive) (countOld : BankArray.Word s.val 972 oldCount)
    (old : WordCleanup.Bounded SourcePayload.parseWords H s.val)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t gv' r,Executes input tape SourcePayload.completeCode cost s t ∧
      cost≤sourceCost p S hm v (sourceInitialWidth p S hm data M H) H oldArchive.length oldCount.length ∧
      SourcePayload.State (sourcePlan physical hp (sourceInitialWidth p S hm data M H) hlen stored) S.n gv' r t ∧
      t.val.output=(sourceStream p S hm).reverse++s.val.output ∧
      GeometryOutput.OutputFrame SourcePayload.completeWork s.val t.val ∧
      WordCleanup.Bounded [972] S.n.bits.length t.val:=by
  let B:=sourceInitialWidth p S hm data M H
  let plan:=sourcePlan physical hp B hlen stored
  have sub : SourcePayload.bank⊆WellStrength.bank:=by decide
  have width0 : WidthBank SourcePayload.bank B (WellStrengthPhysical.values p S hm data):=by
    intro i hi
    exact (WellStrengthPhysical.retained_width p S hm data i (sub hi)).mono (by dsimp [B,sourceInitialWidth];omega)
  have initialWidth : WidthBank SourcePayload.bank B (Function.update (WellStrengthPhysical.values p S hm data) 0 last):=
    width0.update 0 (lastWidth.mono (by dsimp [B,sourceInitialWidth];omega))
  have rhs:=MagnitudeMax.promised_rhs_width p S hp
  have pairWidths:=MagnitudeMax.maximum_width (List.ofFn S.source) (MagnitudeMax.inputWidth p S)
    (MagnitudeMax.inputWidth p S) (MagnitudeMax.inputWidth_pos p S) (fun q hq=>(rhs q hq).1) (fun q hq=>(rhs q hq).2)
  have scaleWidth : (NormalizeRatio.sourceScalePair S).1.bits.length≤B ∧(NormalizeRatio.sourceScalePair S).2.bits.length≤B:=
    ⟨pairWidths.1.trans (by dsimp [B,sourceInitialWidth];omega),pairWidths.2.trans (by dsimp [B,sourceInitialWidth];omega)⟩
  have hraw : Ready SourcePayload.bank (Function.update (WellStrengthPhysical.values p S hm data) 0 last) s:=
    ⟨fun i hi=>raw.1 i (Finset.mem_union.mpr (by
      rcases Finset.mem_union.mp hi with ports|work
      · left;obtain ⟨k,hk,cell⟩:=Finset.mem_biUnion.mp ports;exact Finset.mem_biUnion.mpr ⟨k,sub hk,cell⟩
      · exact Or.inr work)),raw.2⟩
  have oldB : WordCleanup.Bounded SourcePayload.parseWords plan.bankWidth s.val:=by
    intro i hi
    obtain ⟨xs,hxs,word⟩:=old i hi
    exact ⟨xs,hxs.trans (by change H≤sourceBankWidth p S B;dsimp [sourceBankWidth,B,sourceInitialWidth];omega),word⟩
  obtain ⟨cost,t,gv',r,ex,hc,state,out,frame,counter⟩:=SourcePayload.complete_executes plan
    (NormalizeRatio.sourceScalePair S).1 (NormalizeRatio.sourceScalePair S).2 B H
    (by dsimp [B,sourceInitialWidth];omega) (NormalizeRatio.sourceScalePair_positive S hb).1
    (NormalizeRatio.sourceScalePair_positive S hb).2 scaleWidth.1 scaleWidth.2
    (by change 16*(B+1)≤sourceBankWidth p S B;unfold sourceBankWidth;omega)
    gv (WellStrengthPhysical.values p S hm data) last (by simp [WellStrengthPhysical.values]) initialWidth
    (fun i hi=>WellStrengthPhysical.good p S hm data i (sub hi)) (calibrated_mode_nonzero p S hm data)
    (by rw [WellStrengthPhysical.scale,WellStrengthPhysical.midpoint,NormalizeRatio.sourceScalePair_value];rfl)
    input tape s g hraw clean num den precisionWord powerOld templateWord archive
    (by simpa only [plan,sourcePlan,List.length_ofFn] using count) oldArchive oldCount archiveOld countOld oldB
  refine ⟨cost,t,gv',r,ex,?_,?_,?_,frame,?_⟩
  · have cursor:=g.wordWidth 971 (by decide)
    simp only [plan,sourcePlan,SourcePayload.stepCost,List.length_ofFn] at hc
    dsimp only [B] at hc
    unfold sourceCost
    omega
  · simpa only [plan,sourcePlan,List.length_ofFn] using state
  · rw [out,sourcePlan_bytes physical hp B hlen stored geometry length_eq spacing_eq buffer_eq]
  · simpa only [plan,sourcePlan,List.length_ofFn] using counter

#print axioms sources_executes
end Maxwell.Continuum.WellStrengthInitialization
