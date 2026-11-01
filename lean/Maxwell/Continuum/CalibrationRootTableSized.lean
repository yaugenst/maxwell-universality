import Maxwell.Continuum.CalibrationRootTableParameters
import Maxwell.Continuum.CalibrationRootStorageWidths

/-! Allocation widths are derived from the actual coefficient count and
retained scale before generating the root table. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator Calibration
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def scaleWords (v : ℕ→ℕ) (scale : Parts) (i : ℕ) : ℕ :=
  if 1000 ≤ i then dataValues (RootReset.parts scale) i else v i
def widthRequest (v : ℕ→ℕ) (scale : Parts) : ℕ→ℕ :=
  RootStorageWidths.values (scaleWords v scale)

theorem scaleWords_natural (v : ℕ→ℕ) (scale : Parts) (i : ℕ) (hi : i∈allocationIds) :
    scaleWords v scale i=v i := by
  have hh := (show ∀i∈allocationIds,i<1000 by decide) i hi
  simp only [scaleWords,not_le_of_gt hh,ite_false]

theorem scaleWords_components (v : ℕ→ℕ) (scale : Parts) :
    scaleWords v scale 1027=scale.positive ∧ scaleWords v scale 1028=scale.negative ∧
    scaleWords v scale 1029=scale.denominator := by
  simp [scaleWords,dataValues,RootReset.parts]

theorem widthRequest_keep (v : ℕ→ℕ) (scale : Parts) (i : ℕ) (hi : i∈allocationIds)
    (hout : i≠345 ∧ i≠346 ∧ i≠348 ∧ i≠349) : widthRequest v scale i=v i := by
  rw [widthRequest,RootStorageWidths.values_keep _ i hout,scaleWords_natural v scale i hi]

theorem widthRequest_bounds (v : ℕ→ℕ) (scale : Parts) :
    2≤widthRequest v scale 345 ∧ (v 331).bits.length≤widthRequest v scale 345 ∧
    (2*(v 331)^3).bits.length≤widthRequest v scale 345 ∧
    1≤widthRequest v scale 346 ∧ scale.Width (widthRequest v scale 346) := by
  have natural := RootStorageWidths.natural_bounds (scaleWords v scale)
  rw [scaleWords_natural v scale 331 (by decide)] at natural
  have parts := scaleWords_components v scale
  exact ⟨natural.1,natural.2.1,natural.2.2,
    RootStorageWidths.scale_bounds _ scale parts.1 parts.2.1 parts.2.2⟩

theorem width_executes (v : ℕ→ℕ) (scale : Parts) (B : ℕ) (hB : 2≤B)
    (hw : ∀i∈allocationIds,(v i).bits.length≤B) (hscale : scale.Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank allocationIds v s.val)
    (hctx : Context RootReset.bank (v 640) v (RootReset.parts scale) s) :
    ∃cost t,Executes input tape RootStorageWidths.code cost s t ∧
      cost≤RootStorageWidths.costBound B ∧
      NatAssign.Bank allocationIds (widthRequest v scale) t.val ∧
      Context RootReset.bank (v 640) (widthRequest v scale) (RootReset.parts scale) t ∧
      (∀i∈allocationIds,(widthRequest v scale i).bits.length≤RootStorageWidths.outputWidth B) ∧
      BinaryPrecision.Frame RootStorageWidths.changed s.val t.val := by
  have subset : RootParameters.ids⊆allocationIds := by decide
  have width : ∀i∈RootStorageWidths.ids,(scaleWords v scale i).bits.length≤B := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · rw [scaleWords_natural v scale i (subset hi)]
      exact hw i (subset hi)
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      have parts := scaleWords_components v scale
      rcases hi with rfl|rfl|rfl
      · rw [parts.1];exact hscale.1
      · rw [parts.2.1];exact hscale.2.1
      · rw [parts.2.2];exact hscale.2.2
  have bank : NatAssign.Bank RootStorageWidths.ids (scaleWords v scale) s.val := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · rw [scaleWords_natural v scale i (subset hi)]
      exact hb i (subset hi)
    · have lower : 1000 ≤ i := by
        simp only [Finset.mem_insert,Finset.mem_singleton] at hi
        omega
      rw [scaleWords,ite_eq_left lower]
      exact hctx.rational.1 i ((show {1027,1028,1029}⊆ids RootReset.bank by decide) hi)
  obtain ⟨c,t,e,hc,bt,zt,wt,f⟩ := RootStorageWidths.executes (scaleWords v scale) B hB width
    input tape s bank (fun i hi => hctx.scratch i (by omega))
  have af : NatAssign.Bank allocationIds (widthRequest v scale) t.val := by
    intro i hi
    by_cases hm : i∈RootParameters.ids
    · exact bt i (Finset.mem_union_left _ hm)
    have others : i=570 ∨ i=571 ∨ i=572 ∨ i=573 := by
      simp only [allocationIds,RootFrequency.ids,RootParameters.ids,NaturalQuotient.workPorts,
        Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi hm
      omega
    rw [widthRequest_keep v scale i hi (by omega)]
    exact word_of_eq (f.tapes i (by
      simp only [RootStorageWidths.changed,Finset.mem_insert,Finset.mem_singleton];omega)) (hb i hi)
  have zt' : ∀i,i<5→Blank t.val i := by
    intro i hi
    by_cases hs : i<4
    · exact zt i hs
    have eq4 : i=4 := by omega
    subst i
    exact blank_of_eq (f.tapes 4 (by decide)) (hctx.scratch 4 (by decide))
  have keep640 := widthRequest_keep v scale 640 (by decide) (by decide)
  have ctx := hctx.parameter_frame (f.mono (by decide))
    (fun i hi => af i (Finset.mem_union_left _ hi)) zt' (af 640 (by decide))
    (by rw [keep640];exact word_of_eq (f.tapes 653 (by decide)) hctx.phase_precision)
  rw [keep640] at ctx
  refine ⟨c,t,e,hc,af,ctx,?_,f⟩
  intro i hi
  by_cases hm : i∈RootParameters.ids
  · exact wt i (Finset.mem_union_left _ hm)
  have others : i=570 ∨ i=571 ∨ i=572 ∨ i=573 := by
    simp only [allocationIds,RootFrequency.ids,RootParameters.ids,NaturalQuotient.workPorts,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi hm
    omega
  rw [widthRequest_keep v scale i hi (by omega)]
  exact (hw i hi).trans (by
    unfold RootStorageWidths.outputWidth RootStorageWidths.secondWidth RootStorageWidths.firstWidth
    omega)

def sizedCode : Code := .seq RootStorageWidths.code generatedCode
def sizedCost (v : ℕ→ℕ) (scale : Parts) (B H : ℕ) : ℕ := RootStorageWidths.costBound B+
  generatedCost (widthRequest v scale) (RootStorageWidths.outputWidth B) H

theorem sized_executes (v : ℕ→ℕ) [NeZero (v 331)] (degree B H : ℕ)
    (hgrid : v 331=2*degree+1) (hB : 2≤B)
    (hw : ∀i∈allocationIds,(v i).bits.length≤B)
    (hzero : ∀i∈NaturalQuotient.workPorts,v i=0)
    (scale : Parts) (hscale : scale.Valid) (hscaleWidth : scale.Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank allocationIds v s.val)
    (hctx : Context RootReset.bank (v 640) v (RootReset.parts scale) s)
    (hz : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (h201 : Blank s.val 201) (h216 : Blank s.val 216)
    (hheaders : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t,Executes input tape sizedCode cost s t ∧ cost≤sizedCost v scale B H ∧
      Nonempty (TableState (2*(v 331)^3) (v 331) (v 640)
        (widthRequest v scale 345) (widthRequest v scale 346)
        (preparedMetadata (widthRequest v scale)) scale 0 t) ∧
      Blank t.val 201 ∧ t.val.output=s.val.output := by
  obtain ⟨c0,u,e0,hc0,bu,ctxu,wu,f⟩ := width_executes v scale B hB hw hscaleWidth input tape s hb hctx
  have grid := widthRequest_keep v scale 331 (by decide) (by decide)
  have precision := widthRequest_keep v scale 640 (by decide) (by decide)
  have : NeZero (widthRequest v scale 331) := ⟨by rw [grid];exact NeZero.ne (v 331)⟩
  have bounds := widthRequest_bounds v scale
  have zero : ∀i∈NaturalQuotient.workPorts,widthRequest v scale i=0 := by
    intro i hi
    have small : i≤223 := (show ∀i∈NaturalQuotient.workPorts,i≤223 by decide) i hi
    rw [widthRequest_keep v scale i (Finset.mem_union_left _ (Finset.mem_union_left _ hi))
      (by omega),hzero i hi]
  have keep (i : ℕ) (hi : i∈([5,6,7,8,9,37,201,210,212,213,214,215,216]:List ℕ)) :
      u.val.tapes i=s.val.tapes i := by
    apply f.tapes
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    simp only [RootStorageWidths.changed,Finset.mem_insert,Finset.mem_singleton]
    omega
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
      List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto
  have large : 257≤RootStorageWidths.outputWidth B := by
    unfold RootStorageWidths.outputWidth RootStorageWidths.secondWidth RootStorageWidths.firstWidth
    omega
  obtain ⟨c1,t,e1,hc1,table,z201,out⟩ := generated_executes (widthRequest v scale) degree
    (RootStorageWidths.outputWidth B) H (grid.trans hgrid) large bounds.1 bounds.2.2.2.1
    (by rw [grid];exact bounds.2.1) (by rw [grid];exact bounds.2.2.1) wu zero scale hscale
    bounds.2.2.2.2 input tape u bu (by rw [precision];exact ctxu) scratch
    (blank_of_eq (keep 7 (by simp)) h7) (blank_of_eq (keep 37 (by simp)) h37)
    (blank_of_eq (keep 201 (by simp)) h201) (blank_of_eq (keep 216 (by simp)) h216) headers
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add hc0 hc1,?_,z201,out.trans f.output⟩
  simpa only [grid,precision] using table

#print axioms width_executes
#print axioms sized_executes
end Maxwell.Continuum.RationalDataflow.RootTable
