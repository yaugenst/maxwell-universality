import Maxwell.Continuum.CalibrationTableCounts
import Maxwell.Continuum.RationalDataflowWordReplace

/-! The computed table length is copied into the runtime countdown tape.
The source, output allocation, and literal scalar inputs survive this setup. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def tableCounterCode (plan : List NatAssign.Instruction) : Code :=
  .seq (NatAssign.code plan) (WordReplace.code 332 201)

theorem tableCounter_executes {S T : ℕ} (a : PartArray.Table S) (b : PartArray.Table T)
    (plan : List NatAssign.Instruction)
    (hplan : plan=aliasCountPlan ∨ plan=matrixCountPlan ∨ plan=paddedCountPlan)
    (v : ℕ→Parts) (n : ℕ→ℕ) (B : ℕ) (hB : 2≤B)
    (hn : ∀ k∈ids RawFree.neighborRegisters, n k=dataValues v k)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (s : Store)
    (hs : NatAssign.Bank emissionIds n s.val) (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k)
    (ha : a.Ready s) (hb : b.OutputReady s) (hcounter : BankArray.Word s.val 201 xs) :
    ∃ cost t, Executes input tape (tableCounterCode plan) cost s t ∧
      cost≤2^120*(B+xs.length+10)^2 ∧
      NatAssign.Bank emissionIds (NatAssign.values plan n) t.val ∧
      (∀ k∈emissionIds, (NatAssign.values plan n k).bits.length≤countWidth B) ∧
      RationalDataflow.Ready RawFree.neighborRegisters v t ∧ a.Ready t ∧ b.OutputReady t ∧
      (∀ k, k<5 → RationalAccumulator.Blank t.val k) ∧
      BankArray.Word t.val 201 (NatAssign.values plan n 332).bits ∧
      ContinuationFrame s.val t.val := by
  have valid := countPlans_valid plan hplan
  obtain ⟨c0,u,e0,hc0,bank0,blank0,f0⟩ := fixedBankStage_executes emissionIds
    (fun k hk => by have := emissionIds_ge k hk; omega) plan valid.1 (valid.2.2.trans (by decide))
    n B hw (countPlans_literals plan hplan B hB) input tape s hs (fun k hk => hz k (by omega))
  have ready0 : RationalDataflow.Ready RawFree.neighborRegisters v u := by
    refine ⟨?_,blank0⟩
    intro k hk
    have h := bank0 k (emissionIds_parts hk)
    simpa only [countPlans_agrees plan hplan n v hn k hk] using h
  have frame0 := extendFrame emissionIds s u f0
  have a0 := inputReady_emission_frame a s u ha v ready0 frame0
  have b0 := outputReady_emission_frame b s u hb v ready0 frame0
  have width := countPlans_width plan hplan n B hB hw
  have word0 := bank0 332 (by decide)
  obtain ⟨t,e1,word1,f1⟩ := WordReplace.executes 332 201 (by decide) input tape
    (NatAssign.values plan n 332).bits xs u word0
    (BankArray.word_of_eq (f0.tapes 201 (by decide)) hcounter)
  have a1 := a0.copy_frame (Or.inl rfl) f1
  refine ⟨c0+(6*xs.length+15*(NatAssign.values plan n 332).bits.length+21),t,e0.seq e1,?_,?_,width,
    ready0.wordReplace_frame (outside_workspace _ 201 (by decide)) f1,a1,
    b0.copy_frame (Or.inl rfl) f1 a1.scratch a1.seven,?_,word1,?_⟩
  · have hlength := width 332 (by decide)
    unfold stageCost at hc0
    unfold countWidth at hlength
    have hs : (B+2)^2≤(B+xs.length+10)^2 := Nat.pow_le_pow_left (by omega) 2
    have hsum : B+xs.length+1≤(B+xs.length+10)^2 := by
      nlinarith only [Nat.zero_le B,Nat.zero_le xs.length]
    nlinarith only [hc0,hlength,hs,hsum,Nat.zero_le B,Nat.zero_le xs.length]
  · intro k hk
    have hn : k≠201 := by intro he; subst k; exact (by decide : 201∉emissionIds) hk
    exact RationalAccumulator.word_of_eq (f1.2.2.2.2.2.1 k hn) (bank0 k hk)
  · intro k hk
    apply RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 k (by omega))
    by_cases h4 : k<4
    · exact blank0 k h4
    · have he : k=4 := by omega
      subst k
      exact frame_blank_four emissionIds emissionIds_ge s u f0 (hz 4 (by decide))

  · intro k hk
    have h := continuation_external k hk
    exact (f1.2.2.2.2.2.1 k h.2.2.2.1).trans (frame0.tapes k h.2.1)

#print axioms tableCounter_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
