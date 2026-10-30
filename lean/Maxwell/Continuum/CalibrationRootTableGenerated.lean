import Maxwell.Continuum.CalibrationRootTableCounter

/-! A single fixed program allocates and computes the complete rational
root-coefficient table from runtime grid, precision, and scale data. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
attribute [local irreducible] preparedCode tableCode preparedMetadata storageWidth

def generatedCode : Code := .seq preparedCode
  (.seq (NaturalImport.code 570 201) (.seq tableCode (.call (TapeOps.clear 201))))
def generatedCost (v : ℕ→ℕ) (C H : ℕ) : ℕ :=
  preparedCost v C H+(31*(2*(v 331)^3).bits.length+39)+
    tableCost (2*(v 331)^3) (v 331) (v 640) (v 345) (v 346) (preparedMetadata v)
      (2*(v 331)^3).bits.length+(6*(2*(v 331)^3).bits.length+4)

theorem generated_executes (v : ℕ→ℕ) [NeZero (v 331)] (degree C H : ℕ)
    (hgrid : v 331=2*degree+1) (hC : 257≤C)
    (hB : 2≤v 345) (hI : 1≤v 346)
    (hg : (v 331).bits.length≤v 345) (hT : (2*(v 331)^3).bits.length≤v 345)
    (hw : ∀i∈allocationIds,(v i).bits.length≤C)
    (hzero : ∀i∈NaturalQuotient.workPorts,v i=0)
    (scale : Parts) (hscale : scale.Valid) (hscaleWidth : scale.Width (v 346))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank allocationIds v s.val)
    (hctx : Context RootReset.bank (v 640) v (RootReset.parts scale) s)
    (hz : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (h201 : Blank s.val 201) (h216 : Blank s.val 216)
    (hheaders : WordCleanup.Bounded Calibration.PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t,Executes input tape generatedCode cost s t ∧ cost≤generatedCost v C H ∧
      Nonempty (TableState (2*(v 331)^3) (v 331) (v 640) (v 345) (v 346)
        (preparedMetadata v) scale 0 t) ∧ Blank t.val 201 ∧ t.val.output=s.val.output := by
  obtain ⟨c0,s0,e0,h0,a0,ctx0,count0,_,f0⟩ := prepared_executes v C H hC hw hzero scale
    input tape s hb hctx hz h7 h37 h216 hheaders
  have z201 : Blank s0.val 201 := blank_of_eq
    (f0.tapes 201 (by decide)) h201
  obtain ⟨c1,s1,e1,h1,count1,f1⟩ := counter_executes (2*(v 331)^3) input tape s0 count0 z201
  have ctx1 := ctx0.counter_word_frame f1
  have a1 := output_counter_frame a0 f1
  obtain ⟨origin,indexWord⟩ := count1
  have hlen : (2*(v 331)^3).bits.length≤preparedMetadata v := by unfold preparedMetadata;omega
  obtain ⟨c2,s2,last,e2,⟨state⟩,h2,lastWord,lastLength,out2⟩ := table_executes
    (preparedTable v s.val.memory) (v 331) degree (v 640) (v 345) (v 346) (preparedMetadata v)
    hgrid hB hI hg hT scale hscale hscaleWidth (prepared_metadata v s.val.memory)
    (prepared_fit v s.val.memory) (prepared_separated v s.val.memory)
    (2*(v 331)^3).bits origin (addressValue_bits _) hlen input tape s1 ctx1 a1 indexWord
  obtain ⟨t,e3,z3,f3⟩ := RuntimeCounter.clear_executes 201 input tape last origin s2 lastWord
  refine ⟨c0+(c1+(c2+(6*last.length+4))),t,e0.seq (e1.seq (e2.seq e3)),?_,
    ⟨state.counter_word_frame f3⟩,z3,f3.output.trans (out2.trans (f1.output.trans f0.output))⟩
  unfold generatedCost
  rw [lastLength]
  omega

#print axioms generated_executes
end Maxwell.Continuum.RationalDataflow.RootTable
