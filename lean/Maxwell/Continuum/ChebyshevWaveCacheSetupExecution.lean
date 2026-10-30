import Maxwell.Continuum.ChebyshevWaveCacheSetupData

/-! The complete fixed setup executes its dimension scan, metadata copies,
nested phase parameters and actual power-of-two loop. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem cacheSetup_executes (Q N W : ℕ) (hQ : Q.bits.length≤W) (hN : N.bits.length≤W)
    (hW : 6≤W) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank setupIds (initialSetup Q N) s.val) (hz : NatAssign.Scratch s.val)
    (hpower : Blank s.val 144) (hpowerCount : Blank s.val 146) :
    ∃cost t,Executes input tape cacheSetupCode cost s t ∧
      cost≤cacheSetupCost W (waveWorkBits (8*Q) N) ∧
      NatAssign.Bank setupIds (setupValues Q N) t.val ∧ NatAssign.Scratch t.val ∧
      Parameters Q (waveWorkBits (8*Q) N) t ∧
      Word t.val 652 1 ∧ Word t.val 653 (waveWorkBits (8*Q) N) ∧
      Word t.val 681 (waveGrid (8*Q) N) ∧ Word t.val 201 (waveDegree (8*Q) N+1) ∧
      Word t.val 144 (2^waveWorkBits (8*Q) N) ∧ Blank t.val 146 ∧
      BinaryPrecision.Frame setupWorkspace s.val t.val := by
  have hdim : NatAssign.Bank dimensionIds (initialDimensions Q N) s.val := by
    intro i hi
    exact hs i (Finset.mem_union_left _ (Finset.mem_union_left _ hi))
  obtain ⟨c0,s0,e0,h0,b0,z0,f0,_,_,_,_,_,_⟩ := dimensions_executes Q N W hQ hN hW
    input tape s hdim hz
  have bank0 : NatAssign.Bank setupIds (afterDimensions Q N) s0.val := by
    intro i hi
    by_cases hd : i∈dimensionIds
    · simpa only [afterDimensions,ite_eq_left hd] using b0 i hd
    · have hlo := setupIds_ge i hi
      have ho : i∉dimensionWorkspace := by
        intro hm
        rcases Finset.mem_union.mp hm with hsmall|hlarge
        · simp only [Finset.mem_insert,Finset.mem_singleton] at hsmall
          omega
        · exact hd hlarge
      simpa only [afterDimensions,ite_eq_right hd] using word_of_eq (f0.tapes i ho) (hs i hi)
  have hmW : 1≤dimensionWidth W := by unfold dimensionWidth;omega
  obtain ⟨c1,s1,e1,h1,b1,z1,f1⟩ := RationalDataflow.fixedBankStage_executes setupIds setupIds_ge
    handoffInstructions handoffInstructions_valid (by simp [handoffInstructions])
    (afterDimensions Q N) (dimensionWidth W)
    (fun i _ => afterDimensions_width Q N W hQ hN hW i)
    (by simp [handoffInstructions,NatAssign.Instruction.literalWidth];exact hmW)
    input tape s0 bank0 z0
  change NatAssign.Bank setupIds (handoffValues Q N) s1.val at b1
  have parameterInput : NatAssign.Bank parameterIds
      (initialParameters Q (waveWorkBits (8*Q) N)) s1.val := by
    intro i hi
    have hm := b1 i (Finset.mem_union_left _ (Finset.mem_union_right _ hi))
    simpa only [handoffValues_initialParameters Q N i hi] using hm
  have hPw : (waveWorkBits (8*Q) N).bits.length≤dimensionWidth W := by
    simpa only [finalDimensions_work] using finalDimensions_width Q N W hQ hN hW 714 (by decide)
  have hQw : Q.bits.length≤dimensionWidth W := hQ.trans (by unfold dimensionWidth;omega)
  obtain ⟨c2,s2,e2,h2,b2,z2,f2⟩ := parameter_executes Q (waveWorkBits (8*Q) N) (dimensionWidth W)
    hQw hPw (by unfold dimensionWidth;omega) input tape s1 parameterInput z1
  have bank2 : NatAssign.Bank setupIds (setupValues Q N) s2.val := by
    intro i hi
    by_cases hp : i∈parameterIds
    · simpa only [setupValues,ite_eq_left hp] using b2 i hp
    · have hlo := setupIds_ge i hi
      have ho : i∉parameterWorkspace := by
        intro hm
        rcases Finset.mem_union.mp hm with hsmall|hlarge
        · simp only [Finset.mem_insert,Finset.mem_singleton] at hsmall
          omega
        · exact hp hlarge
      simpa only [setupValues,ite_eq_right hp] using word_of_eq (f2.tapes i ho) (b1 i hi)
  have f02 : BinaryPrecision.Frame setupPreparationWorkspace s.val s2.val :=
    (f0.mono (by decide)).trans ((f1.mono (by decide)).trans (f2.mono (by decide)))
  have power2 := blank_of_eq (f02.tapes 144 (by decide)) hpower
  have count2 := blank_of_eq (f02.tapes 146 (by decide)) hpowerCount
  have precision2 : Word s2.val 145 (waveWorkBits (8*Q) N) := by
    simpa only [setupValues_floor_precision] using bank2 145 (by decide)
  obtain ⟨c3,t,e3,h3,p3,power3,count3,f3⟩ :=
    DyadicFloor.StoredPower.power_executes (waveWorkBits (8*Q) N) input tape s2 precision2 count2 power2
  have bank3 : NatAssign.Bank setupIds (setupValues Q N) t.val := by
    intro i hi
    have ho : i∉({144,146}:Finset ℕ) := by
      have disjoint : Disjoint setupIds ({144,146}:Finset ℕ) := by decide
      exact fun h => Finset.disjoint_left.mp disjoint hi h
    exact word_of_eq (f3.tapes i ho) (bank2 i hi)
  have scratch3 : NatAssign.Scratch t.val := by
    intro i hi
    exact blank_of_eq (f3.tapes i (by simp only [Finset.mem_insert,Finset.mem_singleton];omega)) (z2 i hi)
  have parameters3 : Parameters Q (waveWorkBits (8*Q) N) t := by
    intro i hi
    simpa only [setupValues,ite_eq_left hi] using bank3 i (Finset.mem_union_left _ (Finset.mem_union_right _ hi))
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,bank3,scratch3,parameters3,?_,?_,?_,?_,
    power3,count3,(f02.mono (by decide)).trans (f3.mono (by decide))⟩
  · unfold cacheSetupCost
    omega
  · simpa only [setupValues_phase_range] using bank3 652 (by decide)
  · simpa only [setupValues_phase_precision] using bank3 653 (by decide)
  · simpa only [setupValues_grid] using bank3 681 (by decide)
  · simpa only [setupValues_count] using bank3 201 (by decide)

#print axioms cacheSetup_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
