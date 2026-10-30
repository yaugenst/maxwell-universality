import Maxwell.Continuum.FourierTensorModeResetData

/-! Charged restoration of the row-preparation invariant. The bound on
the next row depends on the retained inputs, not on earlier arithmetic. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem reset_executes {m : ℕ} (P R B C : ℕ) (hB : 1≤B)
    (a : Table (2*aliasArraySize R)) (b : Table m) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts)
    (hw : WidthBank RowArithmetic.bank B (values P R a j r v))
    (hg : Good RowArithmetic.bank (values P R a j r v))
    (hnw : ∀i∈ModeIndex.ports,
      (ModeDecode.after (ModeIndex.readValues R a j r v) (ModeIndex.values j R (aliasArraySize R) r.val) i).bits.length≤C)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (s : Store)
    (hr : RationalDataflow.Ready RowArithmetic.bank (values P R a j r v) s)
    (ha : a.Ready s) (hb : b.OutputReady s)
    (hn : NatAssign.Bank ModeIndex.ports
      (ModeDecode.after (ModeIndex.readValues R a j r v) (ModeIndex.values j R (aliasArraySize R) r.val)) s.val)
    (hz : DyadicFloor.Clean s.val) (hp : Word s.val 144 (2^P)) (hc : BankArray.Word s.val 201 word) :
    ∃cost t,Executes input tape resetCode cost s t ∧ cost≤2^110*(B+C+5)^2 ∧
      RationalDataflow.Ready RowArithmetic.bank (canonical v) t ∧ a.Ready t ∧ b.OutputReady t ∧
      NatAssign.Bank ModeIndex.ports (ModeIndex.initial R (aliasArraySize R) 0) t.val ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧ BankArray.Word t.val 201 word ∧
      t.val.tapes 201=s.val.tapes 201 ∧ t.val.output=s.val.output := by
  have htargets : ∀i∈rationalTargets,i∈RowArithmetic.bank := by
    intro i hi
    have hh := (rationalTargets_mem i).mp hi
    exact Finset.mem_range.mpr hh.2
  obtain ⟨c0,s0,e0,hc0,r0,f0⟩ := resetList_executes RowArithmetic.bank rationalTargets htargets
    (values P R a j r v) B hB hw hg input tape s hr
  rw [reset_prepared] at r0
  have ff0 := f0.mono (RoundedInteger.arithmetic_workspace_subset RowArithmetic.bank)
  have a0 := floor_table_frame ha ff0 r0.2
  have b0 := floor_output_frame hb ff0 a0.scratch a0.seven
  have n0 := floor_natural_frame hn ff0
  have z0 := hz.arithmetic_frame f0
  have p0 := RationalAccumulator.word_of_eq
    (f0.tapes 144 (outside_workspace _ _ (by decide))) hp
  have hvalid : ∀i∈naturalTargets,i∈ModeIndex.ports := by
    intro i hi
    simp only [naturalTargets,List.mem_cons,List.not_mem_nil,or_false] at hi
    simp only [ModeIndex.ports,Finset.mem_Icc]
    omega
  obtain ⟨c1,t,e1,hc1,n1,z1,f1⟩ := fixedBankStage_executes ModeIndex.ports
    (fun i hi => by simp only [ModeIndex.ports,Finset.mem_Icc] at hi;omega)
    (NatAssign.clearList naturalTargets) (NatAssign.clearList_valid _ _ hvalid)
    (by decide) _ C hnw (fun a ha => by rw [NatAssign.clearList_literalWidth _ a ha];omega)
    input tape s0 n0 r0.2
  have a1 := ModeIndex.table_frame a0 f1 z1
  refine ⟨c0+c1,t,e0.seq e1,?_,ModeIndex.ready_frame r0 f1 z1,a1,
    ModeIndex.output_frame b0 f1 a1.scratch a1.seven,?_,ModeIndex.floor_frame z0 f1,
    RationalAccumulator.word_of_eq (f1.tapes 144 (by decide)) p0,?_,?_,f1.output.trans f0.output⟩
  · simp only [rationalTargets,List.length_range'] at hc0
    simp only [operationCost,stageCost] at hc0 hc1
    nlinarith only [hc0,hc1,Nat.zero_le B,Nat.zero_le C]
  · intro i hi
    simpa only [reset_naturals R (aliasArraySize R) r.val j (ModeIndex.readValues R a j r v) i hi] using n1 i hi
  · exact BankArray.word_of_eq ((f1.tapes 201 (by decide)).trans
      (f0.tapes 201 (outside_workspace _ _ (by decide)))) hc
  · exact (f1.tapes 201 (by decide)).trans
      (f0.tapes 201 (outside_workspace _ _ (by decide)))

#print axioms reset_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
