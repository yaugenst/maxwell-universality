import Maxwell.Continuum.StoredDecoderPhysicalPlan

/-! Executed complete decoder-description suffix from the produced well
table and the actual selector/header words. No row-loop execution or
preinitialized decoder bank is assumed. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical
open RationalDataflow RealizationParameters SourceDecorationEnumeration
open RationalAccumulator (Word word_of_eq)
set_option maxHeartbeats 6500000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision

def decoderCode : Code:=.seq DecoderRow.initializeCode DecoderRow.descriptionCode
def decoderWork : Finset ℕ:=DecoderRow.initializeWork∪DecoderRow.descriptionWork
def decoderCost (P G B H first count oldIndex oldCountWidth : ℕ) : ℕ:=
  DecoderRow.initializeCost P H+
    (2^22*(G+2)^2+6*oldIndex.bits.length+15*first.bits.length+21+
      (6*oldCountWidth+15*count.bits.length+21)+5*(20*B+24)+1+
      ((count+1)*(13*count.bits.length+15)+count*DecoderRow.stepCost B H))

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
variable {data : WellStrengthPhysical.CalibratedParts p S hm} {v nv : ℕ→ℕ}

theorem decoder_executes {saved} (physical : PhysicalValues p S hm data v saved)
    (hb : S.source≠0) (geometry : Represents S (RealizationParameters.precision p S hm) saved)
    (length_eq : v 2221=length p S hm) (spacing_eq : v 2227=spacing p S hm)
    (buffer_eq : v 2244=bufferSteps p S hm)
    (dimension : nv 500=S.n) (integerBits : nv 4701=(gridReportFormat p S hm).integerBits)
    (fractionalBits : nv 4702=(gridReportFormat p S hm).fractionalBits)
    (sampleCount : nv 4703=gridCount p S hm)
    (side1 : nv 4705=gridSide p S hm 1) (side2 : nv 4706=gridSide p S hm 2)
    (normalization : (nv 4707:ℚ)/(nv 4708)=normalizationScale S)
    {clock : List Bool} (hlen : clock.length=v 1250) {s : Store} {gv : ℕ→ℕ} {rv : ℕ→Parts}
    (g : GeometryOutput.Context (packedVector saved) (v 1252) (v 1250) (geometryBudget v)
      clock (Geometry.values v) gv s)
    (stored : StoredGeometry saved (v 1252) (v 1250) s.val.memory)
    (table : PartArray.Table (siteCount saved))
    (correct : ∀i:Fin (siteCount saved),table.get i=Parts.literal (wellNumerators p S hm i.val:ℚ))
    (R M H : ℕ) (metadata : table.MetadataWidth M)
    (array : table.Ready s) (raw : Ready StoredInteger.slots rv s)
    (rawWidth : WidthBank StoredInteger.slots R rv)
    (selectors : NatAssign.Bank DecoderRow.selectorPorts nv s.val)
    (precisionWord : Word s.val 990 (wellStoredPrecision p S hm))
    (old : WordCleanup.Bounded DecoderRow.outputList H s.val)
    (oldPower : List Bool) (oldPowerWidth : oldPower.length≤H) (power : BankArray.Word s.val 144 oldPower)
    (workspace : WordCleanup.Bounded RationalCanonical.workspace H s.val)
    (firstWord : Word s.val 503 (sourceCircuit S (RealizationParameters.precision p S hm)).size)
    (countWord : Word s.val 500 S.n) (oldIndex : ℕ) (index : Word s.val 728 oldIndex) (one : Word s.val 727 1)
    (oldCounter : List Bool) (counter : BankArray.Word s.val 972 oldCounter)
    (headerWords : ∀k∈DecoderRow.headerPorts,Word s.val k (nv k))
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape decoderCode cost s t ∧
      cost≤decoderCost (wellStoredPrecision p S hm) (geometryBudget v) (decoderBankWidth p S hm v nv R M)
        H (sourceCircuit S (RealizationParameters.precision p S hm)).size S.n oldIndex oldCounter.length ∧
      t.val.output=(Cost.FiniteDecoder.description (decoder p S hm)).reverse++s.val.output ∧
      GeometryOutput.OutputFrame decoderWork s.val t.val:=by
  let B:=decoderBankWidth p S hm v nv R M
  let plan:=decoderPlan physical table R M H metadata normalization hb hlen stored
  have width : WidthBank StoredInteger.slots B rv:=rawWidth.mono (by dsimp [B,decoderBankWidth];omega)
  have selectorWidth : ∀i∈DecoderRow.selectorPorts,(nv i).bits.length≤B:=by
    intro i hi
    exact (decoderSelectorBudget_width nv i (Finset.mem_union_right _ hi)).trans (by dsimp [B,decoderBankWidth];omega)
  obtain ⟨c0,a,e0,hc0,ga,ta,ra,ba,wa,f0⟩:=DecoderRow.initialize_executes g array raw width
    (by dsimp [B,decoderBankWidth];omega) selectors selectorWidth (wellStoredPrecision p S hm) H
    (by dsimp [B,decoderBankWidth];omega) precisionWord old oldPower oldPowerWidth power input tape
  have workspaceA : WordCleanup.Bounded RationalCanonical.workspace H a.val:=by
    intro i hi
    obtain ⟨xs,hxs,word⟩:=workspace i hi
    exact ⟨xs,hxs,BankArray.word_of_eq (f0.tapes i (fun hh=>Finset.disjoint_left.mp (by decide :
      Disjoint RationalCanonical.workspace.toFinset DecoderRow.initializeWork) (by simpa using hi) hh)) word⟩
  have inputs:=(sourceCircuit S (RealizationParameters.precision p S hm)).circuit.inputs_le_size
  have first_le : (sourceCircuit S (RealizationParameters.precision p S hm)).size≤packedLength saved:=by
    unfold packedLength;omega
  have count_le : S.n≤packedLength saved:=inputs.trans first_le
  have firstWidth : (sourceCircuit S (RealizationParameters.precision p S hm)).size.bits.length≤geometryBudget v:=by
    have small : (sourceCircuit S (RealizationParameters.precision p S hm)).size.bits.length≤(packedLength saved).bits.length:=by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size first_le
    exact small.trans plan.countWidth
  have countWidth : S.n.bits.length≤geometryBudget v:=by
    have small : S.n.bits.length≤(packedLength saved).bits.length:=by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size count_le
    exact small.trans plan.countWidth
  have cursorWidth : (3*(sourceCircuit S (RealizationParameters.precision p S hm)).size).bits.length≤geometryBudget v:=by
    have hc : 3*(sourceCircuit S (RealizationParameters.precision p S hm)).size≤packedLength saved:=by
      unfold packedLength;omega
    have small : (3*(sourceCircuit S (RealizationParameters.precision p S hm)).size).bits.length≤(packedLength saved).bits.length:=by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hc
    exact small.trans plan.countWidth
  have headerWidth : ∀i∈DecoderRow.headerPorts,(nv i).bits.length≤B:=by
    intro i hi
    exact (decoderSelectorBudget_width nv i (Finset.mem_union_left _ (by
      simp only [DecoderRow.headerPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega))).trans (by dsimp [B,decoderBankWidth];omega)
  have headerA : ∀i∈DecoderRow.headerPorts,Word a.val i (nv i):=by
    intro i hi
    exact word_of_eq (f0.tapes i (by
      simp only [DecoderRow.headerPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
      simp only [DecoderRow.initializeWork,DecoderRow.outputs,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton,not_or];omega)) (headerWords i hi)
  obtain ⟨c1,t,_,_,_,e1,hc1,out,_,f1⟩:=DecoderRow.description_executes plan
    (sourceCircuit S (RealizationParameters.precision p S hm)).size S.n oldIndex ga ta ra width ba wa
    (decoderPlan_fixed (wellStoredPrecision p S hm) g) workspaceA
    (word_of_eq (f0.tapes 503 (by decide)) firstWord) (word_of_eq (f0.tapes 500 (by decide)) countWord)
    (word_of_eq (f0.tapes 728 (by decide)) index) (word_of_eq (f0.tapes 727 (by decide)) one)
    oldCounter (BankArray.word_of_eq (f0.tapes 972 (by decide)) counter) firstWidth countWidth cursorWidth
    (Geometry.output v).2.2.2.2.2.2.2.2.1 nv headerWidth headerA
    (by unfold siteCount;omega)
    (by unfold packedLength;omega) input tape
  have bytes:=stored_decoder_bytes p S hm geometry plan rfl correct
    (by simp [plan,decoderPlan,decoderConstants,DecoderRow.selectorPorts,Geometry.shift,length_eq,buffer_eq])
    (fun j=>by
      change decoderConstants v nv (wellStoredPrecision p S hm) (983+j.val)=_
      have hj:=j.isLt
      have hn : 983+j.val≠144:=by omega
      have hs : 983+j.val∉DecoderRow.selectorPorts:=by simp only [DecoderRow.selectorPorts,Finset.mem_insert,Finset.mem_singleton];omega
      rw [decoderConstants,ite_eq_right hn,ite_eq_right hs,Geometry.scale,length_eq,spacing_eq])
    (by simpa [plan,decoderPlan,decoderConstants,DecoderRow.selectorPorts] using side1)
    (by simpa [plan,decoderPlan,decoderConstants,DecoderRow.selectorPorts] using side2)
    (by simp [plan,decoderPlan,decoderConstants])
    (by simpa [plan,decoderPlan,decoderConstants,DecoderRow.selectorPorts] using normalization)
    nv dimension integerBits fractionalBits sampleCount hb
  refine ⟨c0+c1,t,e0.seq e1,?_,?_,⟨f1.memory.trans f0.memory,f1.inputHead.trans f0.inputHead,
    f1.randomCursor.trans f0.randomCursor,?_⟩⟩
  · change c1≤2^22*(geometryBudget v+2)^2+6*oldIndex.bits.length+
      15*(sourceCircuit S (RealizationParameters.precision p S hm)).size.bits.length+21+
      (6*oldCounter.length+15*S.n.bits.length+21)+5*(20*B+24)+1+
      ((S.n+1)*(13*S.n.bits.length+15)+S.n*DecoderRow.stepCost B H) at hc1
    dsimp only [B] at hc1
    unfold decoderCost
    omega
  · rw [out,bytes,f0.output]
  · intro i hi
    have hh : i∉DecoderRow.initializeWork ∧i∉DecoderRow.descriptionWork:=by
      simpa only [decoderWork,Finset.mem_union,not_or] using hi
    exact (f1.tapes i hh.2).trans (f0.tapes i hh.1)

#print axioms decoder_executes
end Maxwell.Continuum.WellStrengthInitialization
