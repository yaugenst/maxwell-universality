import Maxwell.Continuum.ChebyshevWaveDimensionsExecution
import Maxwell.Continuum.ChebyshevWaveRuntimeSetup
import Maxwell.Continuum.DyadicFloorPowerPreparation

/-! Stored inputs and the fixed setup schedule for a complete wave cache. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def setupIds : Finset ℕ := dimensionIds∪parameterIds∪{201,652,653,681,145}
def setupPreparationWorkspace : Finset ℕ := {0,1,2,3}∪setupIds
def setupWorkspace : Finset ℕ := {0,1,2,3,144,146}∪setupIds
def initialSetup (Q N : ℕ) : ℕ→ℕ := initialDimensions Q N
def afterDimensions (Q N i : ℕ) : ℕ :=
  if i∈dimensionIds then finalDimensions Q N i else initialSetup Q N i

def handoffInstructions : List NatAssign.Instruction :=
  [.copy 710 670,.copy 714 671,.copy 715 681,.copy 716 201,
   .copy 714 145,.literal 652 1,.copy 714 653]
def handoffValues (Q N : ℕ) : ℕ→ℕ := NatAssign.values handoffInstructions (afterDimensions Q N)
def setupValues (Q N i : ℕ) : ℕ :=
  if i∈parameterIds then parameterValues Q (waveWorkBits (8*Q) N) i else handoffValues Q N i

def cacheSetupCode : Code := .seq dimensionCode (.seq (NatAssign.code handoffInstructions)
  (.seq parameterCode DyadicFloor.StoredPower.powerCode))
def cacheSetupCost (W P : ℕ) : ℕ :=
  2^120*(W+2)^2+RationalDataflow.stageCost (dimensionWidth W)+
    2^50*(dimensionWidth W+2)^2+2^10*(P+2)^2

theorem setupIds_ge (i : ℕ) (hi : i∈setupIds) : 4 ≤ i := by
  simp only [setupIds,dimensionIds,parameterIds,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem handoffInstructions_valid : ∀a∈handoffInstructions,a.Valid setupIds := by
  simp [handoffInstructions,NatAssign.Instruction.Valid,setupIds,dimensionIds,parameterIds]

theorem afterDimensions_width (Q N W : ℕ) (hQ : Q.bits.length≤W) (hN : N.bits.length≤W)
    (hW : 6≤W) (i : ℕ) : (afterDimensions Q N i).bits.length≤dimensionWidth W := by
  by_cases hi : i∈dimensionIds
  · simpa only [afterDimensions,ite_eq_left hi] using finalDimensions_width Q N W hQ hN hW i hi
  · simp only [afterDimensions,ite_eq_right hi,initialSetup]
    exact (initialDimensions_width Q N W hQ hN i).trans (by unfold dimensionWidth;omega)

theorem handoffValues_eq (Q N i : ℕ) : handoffValues Q N i=
    if i=670 then Q else if i=671 then waveWorkBits (8*Q) N else
    if i=681 then waveGrid (8*Q) N else if i=201 then waveDegree (8*Q) N+1 else
    if i=145 then waveWorkBits (8*Q) N else if i=652 then 1 else
    if i=653 then waveWorkBits (8*Q) N else afterDimensions Q N i := by
  have h710 : afterDimensions Q N 710=Q := by
    simp [afterDimensions,dimensionIds,finalDimensions_eq,scannedValues,degreeValues_eq,initialDimensions]
  have h714 : afterDimensions Q N 714=waveWorkBits (8*Q) N := by
    simp [afterDimensions,dimensionIds,finalDimensions_work]
  have h715 : afterDimensions Q N 715=waveGrid (8*Q) N := by
    simp [afterDimensions,dimensionIds,finalDimensions_grid]
  have h716 : afterDimensions Q N 716=waveDegree (8*Q) N+1 := by
    simp [afterDimensions,dimensionIds,finalDimensions_count]
  simp [handoffValues,handoffInstructions,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,h710,h714,h715,h716,Function.update_apply]
  split_ifs <;> omega

theorem handoffValues_initialParameters (Q N i : ℕ) (hi : i∈parameterIds) :
    handoffValues Q N i=initialParameters Q (waveWorkBits (8*Q) N) i := by
  have hr := parameterIds_range i hi
  have hd : i∉dimensionIds := by
    simp only [dimensionIds,Finset.mem_insert,Finset.mem_singleton]
    omega
  simp (disch := omega) [handoffValues_eq,initialParameters,afterDimensions,hd,
    initialSetup,initialDimensions]
  split_ifs <;> omega

theorem setupValues_phase_range (Q N : ℕ) : setupValues Q N 652=1 := by
  simp [setupValues,parameterIds,handoffValues_eq]
theorem setupValues_phase_precision (Q N : ℕ) : setupValues Q N 653=waveWorkBits (8*Q) N := by
  simp [setupValues,parameterIds,handoffValues_eq]
theorem setupValues_grid (Q N : ℕ) : setupValues Q N 681=waveGrid (8*Q) N := by
  simp [setupValues,parameterIds,handoffValues_eq]
theorem setupValues_count (Q N : ℕ) : setupValues Q N 201=waveDegree (8*Q) N+1 := by
  simp [setupValues,parameterIds,handoffValues_eq]
theorem setupValues_floor_precision (Q N : ℕ) : setupValues Q N 145=waveWorkBits (8*Q) N := by
  simp [setupValues,parameterIds,handoffValues_eq]

theorem cacheSetupCost_polynomial (W P : ℕ) : cacheSetupCost W P≤2^160*(W+P+4)^2 := by
  have hsmall : (W+2)^2≤(W+P+4)^2 := Nat.pow_le_pow_left (by omega) 2
  have hp : (P+2)^2≤(W+P+4)^2 := Nat.pow_le_pow_left (by omega) 2
  have hd : dimensionWidth W+2≤2^29*(W+P+4) := by unfold dimensionWidth;omega
  have hs := Nat.pow_le_pow_left hd 2
  unfold cacheSetupCost RationalDataflow.stageCost
  nlinarith only [hsmall,hp,hs,Nat.zero_le ((W+P+4)^2)]

#print axioms handoffValues_eq
#print axioms cacheSetupCost_polynomial
end Maxwell.Continuum.Profile.WaveMachine.Runtime
