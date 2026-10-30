import Maxwell.Continuum.CalibrationArrayDecodeLoad

/-! The existing literal alias decoder also returns its fifth quotient
scratch tape blank, so it can be followed by stored-scale dyadic rounding. -/
namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem decodeLoad_scratch_executes (allIds : Finset ℕ)
    (hIds : ∀k∈allIds,10 ≤ k) (hdecode : ports⊆allIds)
    (hwork : NaturalQuotient.workPorts⊆allIds) (hparts : ids RawFree.stageRegisters⊆allIds)
    (n : ℕ→ℕ) (v : ℕ→Parts) (hn : ∀k∈ids RawFree.stageRegisters,n k=dataValues v k)
    (hzwork : ∀k∈NaturalQuotient.workPorts,n k=0) (B : ℕ) (hB : 2≤B)
    (hw : ∀k∈allIds,(n k).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank allIds n s.val) (hz : ∀k,k<5→RationalAccumulator.Blank s.val k) :
    ∃cost t,Executes input tape decodeLoadCode cost s t ∧ cost≤2^112*(B+5)^2 ∧
      NatAssign.Bank allIds (NatAssign.values coordinateLoad (output n)) t.val ∧
      RationalDataflow.Ready RawFree.stageRegisters (loadedParts v (output n)) t ∧
      RationalAccumulator.Blank t.val 4 ∧
      BinaryPrecision.Frame ({0,1,2,3,4}∪allIds) s.val t.val := by
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := executes allIds hIds hdecode hwork n hzwork B hB hw input tape s hb hz
  have w0 := output_width n allIds hdecode B hw
  obtain ⟨c1,t,e1,hc1,b1,r1,f1⟩ := coordinateLoad_executes allIds
    (fun k hk => by have := hIds k hk;omega) hdecode hparts (output n) v (output_agrees n v hn)
    (2*B+8) (by omega) w0 input tape u b0 (fun k hk => z0 k (by omega))
  have h4 : 4∉({0,1,2,3}∪allIds) := by
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
    refine ⟨by omega,?_⟩
    intro hh
    have := hIds 4 hh
    omega
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,r1,
    RationalAccumulator.blank_of_eq (f1.tapes 4 h4) (z0 4 (by decide)),f0.trans (f1.mono ?_)⟩
  · have hsq : (2*B+8+2)^2=4*(B+5)^2 := by ring
    rw [hsq] at hc1
    nlinarith only [hc0,hc1,Nat.zero_le ((B+5)^2)]
  · intro k hk
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hk ⊢
    tauto

#print axioms decodeLoad_scratch_executes
end Maxwell.Continuum.Calibration.ArrayDecodeMachine
