import Maxwell.Continuum.CalibrationRootParameterMachine
import Maxwell.Continuum.CalibrationRootTableGenerated

/-! Compute the root sampling request from its stored scale and precision,
then run the actual coefficient-table allocator and evaluator. The glue and
phase evaluators receive the same computed sampling precision. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open Calibration
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
attribute [local irreducible] MasterConstants.exponent

def parameterCode : Code := .seq RootParameters.code (WordReplace.code 640 653)
def parameterChanged : Finset ℕ := RootParameters.workspace∪{653}
def parameterCost (v : ℕ→ℕ) (B : ℕ) : ℕ := RootParameters.costBound B+
  (6*(v 640).bits.length+15*(RootParameters.values v 640).bits.length+21)

theorem parameterCost_polynomial (v : ℕ→ℕ) (B : ℕ)
    (old : (v 640).bits.length≤B)
    (computed : (RootParameters.values v 640).bits.length≤RootParameters.outputWidth B) :
    parameterCost v B≤2^151*(B+2)^2 := by
  have width := computed.trans (RootParameters.outputWidth_linear B)
  have base := RootParameters.costBound_polynomial B
  have square : B+2≤(B+2)^2 := Nat.le_self_pow (by decide) _
  unfold parameterCost
  nlinarith only [old,width,base,square,Nat.zero_le B]

private theorem parameter_small (i : ℕ) (hi : i∈parameterChanged) :
    i<5 ∨ (220 ≤ i ∧ i≤653) := by
  simp only [parameterChanged,RootParameters.workspace,RootParameters.ids,NaturalQuotient.workPorts,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
  omega

theorem Context.parameter_frame {S : Finset ℕ} {N : ℕ} {n m : ℕ→ℕ} {v : ℕ→Parts}
    {s t : Store} (h : Context S N n v s)
    (f : BinaryPrecision.Frame parameterChanged s.val t.val)
    (hb : NatAssign.Bank RootFrequency.ids m t.val) (hz : ∀i,i<5→Blank t.val i)
    (hg : Word t.val 640 (m 640)) (hp : Word t.val 653 (m 640)) :
    Context S (m 640) m v t := by
  have rational : Ready S v t := by
    refine ⟨?_,fun i hi => hz i (by omega)⟩
    intro i hi
    have hlo := ids_ge_ten S i hi
    apply word_of_eq (f.tapes i _) (h.rational.1 i hi)
    intro hm
    have ha := parameter_small i hm
    exact outside_workspace S i (Or.inr (by omega)) (Finset.mem_union_right _ hi)
  have glue : Glue.Clean t.val := by
    intro i hi
    by_cases hs : i<5
    · exact hz i hs
    have disjoint : Disjoint ((GlueMachine.Runtime.ids.erase 640)\Finset.range 5)
        parameterChanged := by decide
    have hout := Finset.disjoint_left.mp disjoint
      (Finset.mem_sdiff.mpr ⟨hi,by simpa only [Finset.mem_range] using hs⟩)
    exact blank_of_eq (f.tapes i hout) (h.glue i hi)
  have phase : Phase.Runtime.Clean t.val := by
    intro i hi
    by_cases hs : i<5
    · exact hz i hs
    have disjoint : Disjoint (((PhaseMachine.Runtime.ids.erase 652).erase 653)\Finset.range 5)
        parameterChanged := by decide
    have hout := Finset.disjoint_left.mp disjoint
      (Finset.mem_sdiff.mpr ⟨hi,by simpa only [Finset.mem_range] using hs⟩)
    exact blank_of_eq (f.tapes i hout) (h.phase i hi)
  exact ⟨rational,hb,hz,glue,phase,hg,word_of_eq (f.tapes 652 (by decide)) h.phase_range,hp⟩

theorem parameter_executes (v : ℕ→ℕ) (B : ℕ)
    (hB : 3*MasterConstants.exponent+4≤B) (denominator : 0<v 332)
    (hw : ∀i∈allocationIds,(v i).bits.length≤B)
    (hzero : ∀i∈NaturalQuotient.workPorts,v i=0)
    (scale : Parts) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank allocationIds v s.val)
    (hctx : Context RootReset.bank (v 640) v (RootReset.parts scale) s) :
    ∃cost t,Executes input tape parameterCode cost s t ∧ cost≤parameterCost v B ∧
      NatAssign.Bank allocationIds (RootParameters.values v) t.val ∧
      Context RootReset.bank (RootParameters.values v 640) (RootParameters.values v)
        (RootReset.parts scale) t ∧
      (∀i∈allocationIds,(RootParameters.values v i).bits.length≤RootParameters.outputWidth B) ∧
      BinaryPrecision.Frame parameterChanged s.val t.val := by
  have subset : RootParameters.ids⊆allocationIds := by decide
  obtain ⟨c0,u,e0,hc0,bu,zu,wu,f0⟩ := RootParameters.executes v B hB denominator
    (fun i hi => hw i (subset hi)) hzero
    input tape s (fun i hi => hb i (subset hi)) hctx.scratch
  have au : NatAssign.Bank allocationIds (RootParameters.values v) u.val := by
    intro i hi
    by_cases hm : i∈RootParameters.ids
    · exact bu i hm
    have lower : 220 ≤ i := (show ∀i∈allocationIds,220 ≤ i by decide) i hi
    have unchanged : RootParameters.values v i=v i := RootParameters.values_keep v i (by
      simp only [RootParameters.ids,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.mem_Icc] at hm
      omega)
    rw [unchanged]
    apply word_of_eq (f0.tapes i _) (hb i hi)
    simp only [RootParameters.workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    exact not_or_intro (by omega) hm
  have old : Word u.val 653 (v 640) := word_of_eq (f0.tapes 653 (by decide)) hctx.phase_precision
  obtain ⟨t,e1,pt,f1⟩ := WordReplace.executes 640 653 (by decide) input tape
    (RootParameters.values v 640).bits (v 640).bits u (bu 640 (by decide)) old
  have copyFrame : BinaryPrecision.Frame {653} u.val t.val := StoredParts.copy_frame f1
  have frame : BinaryPrecision.Frame parameterChanged s.val t.val :=
    (f0.mono Finset.subset_union_left).trans (copyFrame.mono Finset.subset_union_right)
  have bank : NatAssign.Bank allocationIds (RootParameters.values v) t.val := by
    intro i hi
    exact word_of_eq (copyFrame.tapes i (by
      have := (show ∀i∈allocationIds,i≠653 by decide) i hi
      simpa using this)) (au i hi)
  have zt (i : ℕ) (hi : i<5) : Blank t.val i :=
    blank_of_eq (copyFrame.tapes i (by simp only [Finset.mem_singleton];omega)) (zu i hi)
  have context := hctx.parameter_frame frame
    (fun i hi => bank i (Finset.mem_union_left _ hi)) zt (bank 640 (by decide)) pt
  have width : ∀i∈allocationIds,(RootParameters.values v i).bits.length≤RootParameters.outputWidth B := by
    intro i hi
    by_cases hm : i∈RootParameters.ids
    · exact wu i hm
    rw [RootParameters.values_keep v i (by
      simp only [RootParameters.ids,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.mem_Icc] at hm
      omega)]
    exact (hw i hi).trans (RootParameters.inputWidth_le_outputWidth B)
  exact ⟨c0+(6*(v 640).bits.length+15*(RootParameters.values v 640).bits.length+21),t,
    e0.seq e1,Nat.add_le_add_right hc0 _,bank,context,width,frame⟩

instance parameterGrid_neZero (v : ℕ→ℕ) : NeZero (RootParameters.values v 331) :=
  ⟨by rw [(RootParameters.values_outputs v).2.1];unfold RootParameters.grid;omega⟩

def requestedCode : Code := .seq parameterCode generatedCode
def requestedCost (v : ℕ→ℕ) (B H : ℕ) : ℕ :=
  parameterCost v B+generatedCost (RootParameters.values v) (RootParameters.outputWidth B) H

theorem requested_parameters (v : ℕ→ℕ) (denominator : 0<v 332) :
    RootParameters.values v 331=rootSamplingGrid ((v 330:ℚ)/v 332) (v 333) (v 334) ∧
    RootParameters.values v 640=rootSamplingBits ((v 330:ℚ)/v 332) (v 333) (v 334) := by
  have values := RootParameters.values_outputs v
  exact ⟨values.2.1.trans (RootParameters.grid_eq _ _ _ _ denominator),
    values.2.2.trans (RootParameters.bits_eq _ _ _ _ denominator)⟩

theorem scalar_computed (grid P : ℕ) [NeZero grid] (scale : ℚ) (N ell index : ℕ)
    (hgrid : grid=rootSamplingGrid scale N ell) (hprecision : P=rootSamplingBits scale N ell) :
    scalar grid scale P index=
      if index%2=0 then
        (computedRootCoefficient scale N ell (RootFrequency.frequency grid index)).re.center
      else (computedRootCoefficient scale N ell (RootFrequency.frequency grid index)).im.center := by
  subst grid P
  rfl

theorem TableState.computed_correct {T grid P B I W : ℕ} [NeZero grid]
    {scale : Parts} {s : Store} (h : TableState T grid P B I W scale 0 s)
    (N ell : ℕ) (hgrid : grid=rootSamplingGrid scale.value N ell)
    (hprecision : P=rootSamplingBits scale.value N ell) (i : Fin T) :
    (h.table.get i).Valid ∧ (h.table.get i).Width (entryWidth grid P B I) ∧
      (h.table.get i).value=
        if i.val%2=0 then
          (computedRootCoefficient scale.value N ell (RootFrequency.frequency grid i.val)).re.center
        else (computedRootCoefficient scale.value N ell (RootFrequency.frequency grid i.val)).im.center := by
  obtain ⟨valid,width,value⟩ := h.correct i (Nat.zero_le _)
  exact ⟨valid,width,value.trans (scalar_computed grid P scale.value N ell i.val hgrid hprecision)⟩

attribute [local irreducible] RootParameters.values RootParameters.degree RootParameters.grid
  RootParameters.bits RootParameters.numerator

theorem requested_executes (v : ℕ→ℕ) (B H : ℕ)
    (hB : 3*MasterConstants.exponent+4≤B) (denominator : 0<v 332)
    (hw : ∀i∈allocationIds,(v i).bits.length≤B)
    (hzero : ∀i∈NaturalQuotient.workPorts,v i=0)
    (hnatural : 2≤RootParameters.values v 345) (hI : 1≤RootParameters.values v 346)
    (hgridWidth : (RootParameters.values v 331).bits.length≤RootParameters.values v 345)
    (hcountWidth : (2*(RootParameters.values v 331)^3).bits.length≤RootParameters.values v 345)
    (scale : Parts) (hscale : scale.Valid) (hscaleWidth : scale.Width (RootParameters.values v 346))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank allocationIds v s.val)
    (hctx : Context RootReset.bank (v 640) v (RootReset.parts scale) s)
    (hz : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (h201 : Blank s.val 201) (h216 : Blank s.val 216)
    (hheaders : WordCleanup.Bounded Calibration.PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t,Executes input tape requestedCode cost s t ∧ cost≤requestedCost v B H ∧
      Nonempty (TableState (2*(RootParameters.values v 331)^3) (RootParameters.values v 331)
        (RootParameters.values v 640) (RootParameters.values v 345) (RootParameters.values v 346)
        (preparedMetadata (RootParameters.values v)) scale 0 t) ∧
      Blank t.val 201 ∧ t.val.output=s.val.output := by
  obtain ⟨c0,u,e0,hc0,bu,ctxu,htable,f0⟩ := parameter_executes v B hB denominator hw hzero scale
    input tape s hb hctx
  have keep (i : ℕ) (hi : i∈([5,6,7,8,9,37,201,210,212,213,214,215,216]:List ℕ)) :
      u.val.tapes i=s.val.tapes i := by
    apply f0.tapes
    intro hm
    have hh := parameter_small i hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  have scratch : BankArray.Scratch u.val := by
    rcases hz with ⟨_,_,_,_,h5,h6,h8,h9⟩
    exact ⟨ctxu.scratch 0 (by decide),ctxu.scratch 1 (by decide),ctxu.scratch 2 (by decide),
      ctxu.scratch 3 (by decide),blank_of_eq (keep 5 (by simp)) h5,
      blank_of_eq (keep 6 (by simp)) h6,blank_of_eq (keep 8 (by simp)) h8,
      blank_of_eq (keep 9 (by simp)) h9⟩
  have headers : WordCleanup.Bounded Calibration.PowerMachine.BufferNorm.Allocation.clearHeaders H u.val := by
    intro i hi
    obtain ⟨xs,hxs,word⟩ := hheaders i hi
    refine ⟨xs,hxs,BankArray.word_of_eq (keep i ?_) word⟩
    simp only [Calibration.PowerMachine.BufferNorm.Allocation.clearHeaders,
      List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto
  have grid : RootParameters.values v 331=2*RootParameters.degree (v 330) (v 332) (v 333) (v 334)+1 :=
    by simpa only [RootParameters.grid] using (RootParameters.values_outputs v).2.1
  have hC : 257≤RootParameters.outputWidth B := by
    unfold RootParameters.outputWidth RootParameters.secondWidth RootParameters.firstWidth
    omega
  obtain ⟨c1,t,e1,hc1,table,z201,out⟩ := generated_executes (RootParameters.values v)
    (RootParameters.degree (v 330) (v 332) (v 333) (v 334)) (RootParameters.outputWidth B) H grid hC hnatural hI
    hgridWidth hcountWidth htable (RootParameters.values_work_zero v hzero) scale hscale hscaleWidth
    input tape u bu ctxu scratch (blank_of_eq (keep 7 (by simp)) h7)
    (blank_of_eq (keep 37 (by simp)) h37) (blank_of_eq (keep 201 (by simp)) h201)
    (blank_of_eq (keep 216 (by simp)) h216) headers
  exact ⟨c0+c1,t,e0.seq e1,Nat.add_le_add hc0 hc1,table,z201,out.trans f0.output⟩

#print axioms parameter_executes
#print axioms requested_executes
#print axioms TableState.computed_correct
end Maxwell.Continuum.RationalDataflow.RootTable
