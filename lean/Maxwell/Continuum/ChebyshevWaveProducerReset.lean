import Maxwell.Continuum.ChebyshevWaveProducerMetadata

/-! Charged restoration of the runtime parameter bank after a generated
coefficient has been fetched. Q and N remain stored for the next factor. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def resetIds : Finset ℕ := setupIds∪{144,146}
def resetTargets : List ℕ := [712,713,714,715,716,717,718,719,
  670,671,672,673,674,675,676,677,678,679,201,652,653,681,145,144,146]
def resetInstructions : List NatAssign.Instruction := resetTargets.map (fun i => .literal i 0)
def resetCode : Code := NatAssign.code resetInstructions
def completedSetup (Q N i : ℕ) : ℕ :=
  if i=144 then 2^waveWorkBits (8*Q) N else if i=146 ∨ i=201 then 0 else setupValues Q N i
def resetWidth (Q N W : ℕ) : ℕ := dimensionWidth W+2*Q+waveWorkBits (8*Q) N+32

theorem zero_list_values (targets : List ℕ) (v : ℕ→ℕ) (i : ℕ) :
    NatAssign.values (targets.map (fun k => NatAssign.Instruction.literal k 0)) v i=
      if i∈targets then 0 else v i := by
  induction targets generalizing v with
  | nil => simp [NatAssign.values]
  | cons k rest ih =>
    simp only [List.map_cons,NatAssign.values,ih,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,List.mem_cons]
    by_cases hik : i=k <;> by_cases hir : i∈rest <;> simp [hik,hir]

theorem resetTargets_mem (i : ℕ) : i∈resetTargets ↔ i∈resetIds ∧ i≠710 ∧ i≠711 := by
  simp only [resetTargets,resetIds,setupIds,dimensionIds,parameterIds,List.mem_cons,List.not_mem_nil,
    or_false,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem reset_values (Q N i : ℕ) (hi : i∈resetIds) :
    NatAssign.values resetInstructions (completedSetup Q N) i=initialSetup Q N i := by
  rw [resetInstructions,zero_list_values]
  simp only [resetTargets_mem]
  by_cases hiQ : i=710
  · subst i
    simp [completedSetup,setupValues,parameterIds,handoffValues_eq,afterDimensions,dimensionIds,
      finalDimensions_eq,scannedValues,degreeValues_eq,initialSetup,initialDimensions]
  · by_cases hiN : i=711
    · subst i
      simp [completedSetup,setupValues,parameterIds,handoffValues_eq,afterDimensions,dimensionIds,
        finalDimensions_eq,scannedValues,degreeValues_eq,initialSetup,initialDimensions]
    · simp [hi,hiQ,hiN,initialSetup,initialDimensions]

theorem completedSetup_width (Q N W : ℕ) (hQ : Q.bits.length ≤ W) (hN : N.bits.length ≤ W)
    (hW : 6 ≤ W) (i : ℕ) : (completedSetup Q N i).bits.length ≤ resetWidth Q N W := by
  have hpower : (2^waveWorkBits (8*Q) N).bits.length=waveWorkBits (8*Q) N+1 := by
    rw [Nat.size_eq_bits_len,Nat.size_pow]
  have hafter := afterDimensions_width Q N W hQ hN hW i
  have hparam := parameterValues_width Q (waveWorkBits (8*Q) N) i
  have hwork := finalDimensions_width Q N W hQ hN hW 714 (by decide)
  rw [finalDimensions_work] at hwork
  have hgrid := finalDimensions_width Q N W hQ hN hW 715 (by decide)
  rw [finalDimensions_grid] at hgrid
  have hcount := finalDimensions_width Q N W hQ hN hW 716 (by decide)
  rw [finalDimensions_count] at hcount
  have hB : dimensionWidth W ≤ resetWidth Q N W := by unfold resetWidth;omega
  have hQB : W ≤ resetWidth Q N W := by unfold resetWidth dimensionWidth;omega
  have hPB : waveWorkBits (8*Q) N+1 ≤ resetWidth Q N W := by unfold resetWidth;omega
  have hparB : 2*Q+waveWorkBits (8*Q) N+12 ≤ resetWidth Q N W := by unfold resetWidth;omega
  have h1B : 1 ≤ resetWidth Q N W := by unfold resetWidth;omega
  by_cases h144 : i=144
  · simp only [completedSetup,h144,ite_true,hpower];exact hPB
  by_cases hzero : i=146 ∨ i=201
  · simp only [completedSetup,h144,ite_false,hzero,ite_true]
    exact Nat.zero_le _
  simp only [completedSetup,h144,ite_false,hzero]
  by_cases hpar : i∈parameterIds
  · simpa only [setupValues,ite_eq_left hpar] using hparam.trans hparB
  simp only [setupValues,ite_eq_right hpar,handoffValues_eq]
  split_ifs
  · exact hQ.trans hQB
  · exact hwork.trans hB
  · exact hgrid.trans hB
  · exact hcount.trans hB
  · exact hwork.trans hB
  · simpa using h1B
  · exact hwork.trans hB
  · exact hafter.trans hB

theorem CacheState.completed_bank {n Q N D W : ℕ} {a : Table n} {q : ℚ}
    {base : ℕ→Parts} {initial : Table (2*D)} {s : Store}
    (h : CacheState a q Q N D W base initial 0 s)
    (hp : NatAssign.Bank persistentSetupIds (setupValues Q N) s.val)
    (hc : Blank s.val 201) (hz : Blank s.val 146) :
    NatAssign.Bank resetIds (completedSetup Q N) s.val := by
  intro i hi
  by_cases h144 : i=144
  · subst i;simpa only [completedSetup,ite_true] using h.power
  by_cases h146 : i=146
  · subst i;simpa [completedSetup,Word,Blank] using hz
  by_cases h201 : i=201
  · subst i;simpa [completedSetup,Word,Blank] using hc
  simp only [completedSetup,h144,h146,h201,or_self,ite_false]
  by_cases hper : i∈persistentSetupIds
  · exact hp i hper
  by_cases hpar : i∈parameterIds
  · simpa only [setupValues,ite_eq_left hpar] using h.ready.parameters i hpar
  have hi' : i=652 ∨ i=653 ∨ i=681 := by
    simp only [resetIds,setupIds,persistentSetupIds,dimensionIds,parameterIds,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hi hper hpar
    omega
  rcases hi' with rfl|rfl|rfl
  · simpa only [setupValues_phase_range] using h.ready.rangeWord
  · simpa only [setupValues_phase_precision] using h.ready.precisionWord
  · simpa only [setupValues_grid] using h.grid

theorem reset_executes (Q N W : ℕ) (hQ : Q.bits.length ≤ W) (hN : N.bits.length ≤ W)
    (hW : 6 ≤ W) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank resetIds (completedSetup Q N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape resetCode cost s t ∧ cost ≤ RationalDataflow.stageCost (resetWidth Q N W) ∧
      NatAssign.Bank setupIds (initialSetup Q N) t.val ∧ Blank t.val 144 ∧ Blank t.val 146 ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame setupWorkspace s.val t.val := by
  obtain ⟨c,t,e,hc,bt,zt,ft⟩ := fixedBankStage_executes resetIds (by
      intro i hi;simp only [resetIds,setupIds,dimensionIds,parameterIds,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi;omega)
    resetInstructions (by simp [resetInstructions,resetTargets,NatAssign.Instruction.Valid,resetIds,
      setupIds,dimensionIds,parameterIds]) (by decide) (completedSetup Q N) (resetWidth Q N W)
    (fun i _ => completedSetup_width Q N W hQ hN hW i)
    (by simp [resetInstructions,resetTargets,NatAssign.Instruction.literalWidth]) input tape s hs hz
  have bank : NatAssign.Bank resetIds (initialSetup Q N) t.val := by
    intro i hi
    simpa only [reset_values Q N i hi] using bt i hi
  refine ⟨c,t,e,hc,fun i hi => bank i (Finset.mem_union_left _ hi),?_,?_,zt,ft.mono (by decide)⟩
  · simpa [initialSetup,initialDimensions,Word,Blank] using bank 144 (by decide)
  · simpa [initialSetup,initialDimensions,Word,Blank] using bank 146 (by decide)

#print axioms reset_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
