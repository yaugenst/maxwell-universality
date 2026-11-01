import Maxwell.Continuum.CalibrationRootTableSized

/-! One fixed program computes degree, grid, precision, storage widths,
allocation and every root coefficient from the retained scalar inputs. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator Calibration
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
attribute [local irreducible] MasterConstants.exponent RootParameters.values
  RootParameters.degree RootParameters.grid RootParameters.bits RootParameters.numerator

def computedCode : Code := .seq parameterCode sizedCode
def computedCost (v : ℕ→ℕ) (scale : Parts) (B H : ℕ) : ℕ :=
  parameterCost v B+sizedCost (RootParameters.values v) scale (RootParameters.outputWidth B) H

theorem computed_executes (v : ℕ→ℕ) (B H : ℕ)
    (hB : 3*MasterConstants.exponent+4≤B) (denominator : 0<v 332)
    (hw : ∀i∈allocationIds,(v i).bits.length≤B)
    (hzero : ∀i∈NaturalQuotient.workPorts,v i=0)
    (scale : Parts) (hscale : scale.Valid) (hscaleWidth : scale.Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank allocationIds v s.val)
    (hctx : Context RootReset.bank (v 640) v (RootReset.parts scale) s)
    (hz : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (h201 : Blank s.val 201) (h216 : Blank s.val 216)
    (hheaders : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t,Executes input tape computedCode cost s t ∧ cost≤computedCost v scale B H ∧
      Nonempty (TableState (2*(RootParameters.values v 331)^3) (RootParameters.values v 331)
        (RootParameters.values v 640) (widthRequest (RootParameters.values v) scale 345)
        (widthRequest (RootParameters.values v) scale 346)
        (preparedMetadata (widthRequest (RootParameters.values v) scale)) scale 0 t) ∧
      Blank t.val 201 ∧ t.val.output=s.val.output := by
  obtain ⟨c0,u,e0,hc0,bu,ctxu,wu,f⟩ := parameter_executes v B hB denominator hw hzero scale
    input tape s hb hctx
  have keep (i : ℕ) (hi : i∈([5,6,7,8,9,37,201,210,212,213,214,215,216]:List ℕ)) :
      u.val.tapes i=s.val.tapes i := f.tapes i
    ((show ∀i∈([5,6,7,8,9,37,201,210,212,213,214,215,216]:List ℕ),i∉parameterChanged by decide) i hi)
  have scratch : BankArray.Scratch u.val := by
    rcases hz with ⟨_,_,_,_,h5,h6,h8,h9⟩
    exact ⟨ctxu.scratch 0 (by decide),ctxu.scratch 1 (by decide),ctxu.scratch 2 (by decide),
      ctxu.scratch 3 (by decide),blank_of_eq (keep 5 (by simp)) h5,
      blank_of_eq (keep 6 (by simp)) h6,blank_of_eq (keep 8 (by simp)) h8,
      blank_of_eq (keep 9 (by simp)) h9⟩
  have headers : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H u.val := by
    intro i hi
    obtain ⟨xs,hxs,word⟩ := hheaders i hi
    refine ⟨xs,hxs,BankArray.word_of_eq (keep i ?_) word⟩
    simp only [PowerMachine.BufferNorm.Allocation.clearHeaders,
      List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> simp
  have grid : RootParameters.values v 331=2*RootParameters.degree (v 330) (v 332) (v 333) (v 334)+1 :=
    by simpa only [RootParameters.grid] using (RootParameters.values_outputs v).2.1
  have big : 2≤RootParameters.outputWidth B := by
    unfold RootParameters.outputWidth RootParameters.secondWidth RootParameters.firstWidth
    omega
  obtain ⟨c1,t,e1,hc1,table,z201,out⟩ := sized_executes (RootParameters.values v)
    (RootParameters.degree (v 330) (v 332) (v 333) (v 334)) (RootParameters.outputWidth B) H grid big
    wu (RootParameters.values_work_zero v hzero) scale hscale
    (hscaleWidth.mono (RootParameters.inputWidth_le_outputWidth B)) input tape u bu ctxu scratch
    (blank_of_eq (keep 7 (by simp)) h7) (blank_of_eq (keep 37 (by simp)) h37)
    (blank_of_eq (keep 201 (by simp)) h201) (blank_of_eq (keep 216 (by simp)) h216) headers
  exact ⟨c0+c1,t,e0.seq e1,Nat.add_le_add hc0 hc1,table,z201,out.trans f.output⟩

theorem TableState.computed_request {v : ℕ→ℕ} {scale : Parts} {B I W : ℕ} {t : Store}
    (h : TableState (2*(RootParameters.values v 331)^3) (RootParameters.values v 331)
      (RootParameters.values v 640) B I W scale 0 t)
    (denominator : 0<v 332) (hscale : scale.value=(v 330:ℚ)/v 332)
    (i : Fin (2*(RootParameters.values v 331)^3)) :
    (h.table.get i).Valid ∧
      (h.table.get i).Width (entryWidth (RootParameters.values v 331) (RootParameters.values v 640) B I) ∧
      (h.table.get i).value=
        if i.val%2=0 then (computedRootCoefficient scale.value (v 333) (v 334)
          (RootFrequency.frequency (RootParameters.values v 331) i.val)).re.center
        else (computedRootCoefficient scale.value (v 333) (v 334)
          (RootFrequency.frequency (RootParameters.values v 331) i.val)).im.center := by
  have parameters := requested_parameters v denominator
  exact h.computed_correct (v 333) (v 334) (by rw [hscale];exact parameters.1)
    (by rw [hscale];exact parameters.2) i

#print axioms computed_executes
#print axioms TableState.computed_request
end Maxwell.Continuum.RationalDataflow.RootTable
