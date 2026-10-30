import Maxwell.Continuum.ChebyshevWaveRounded
import Maxwell.Continuum.NaturalBankStage
import Maxwell.Continuum.StoredWordLength

/-! Fixed runtime calculation of the wave degree, precision and Fourier
grid. The input bank represents Q and N explicitly; its other ports are zero. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def dimensionIds : Finset ℕ := {710,711,712,713,714,715,716,717,718,719}
def dimensionWorkspace : Finset ℕ := {0,1,2,3}∪dimensionIds
def initialDimensions (Q N i : ℕ) : ℕ := if i=710 then Q else if i=711 then N else 0

def degreeSetup : List NatAssign.Instruction :=
  [.copy 710 712,.literal 717 8,.multiply 717 712,.add 711 712,
   .literal 717 16,.add 717 712,.multiply 717 712,.literal 717 0]
def degreeValues (Q N : ℕ) : ℕ→ℕ := NatAssign.values degreeSetup (initialDimensions Q N)
def scannedValues (Q N : ℕ) : ℕ→ℕ :=
  Function.update (degreeValues Q N) 713 (waveDegree (8*Q) N).bits.length

def gridSetup : List NatAssign.Instruction :=
  [.copy 711 714,.add 713 714,.literal 717 32,.add 717 714,
   .copy 710 715,.literal 717 8,.multiply 717 715,.add 714 715,
   .literal 717 16,.add 717 715,.multiply 717 715,.add 712 715,
   .literal 717 1,.add 717 715,.copy 712 716,.add 717 716,.literal 717 0]
def finalDimensions (Q N : ℕ) : ℕ→ℕ := NatAssign.values gridSetup (scannedValues Q N)
def dimensionCode : Code := .seq (NatAssign.code degreeSetup)
  (.seq (WordLength.code 712 713) (NatAssign.code gridSetup))

theorem dimensionIds_ge (i : ℕ) (hi : i∈dimensionIds) : 4 ≤ i := by
  simp only [dimensionIds,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem degreeSetup_valid : ∀a∈degreeSetup,a.Valid dimensionIds := by
  simp [degreeSetup,NatAssign.Instruction.Valid,dimensionIds]

theorem gridSetup_valid : ∀a∈gridSetup,a.Valid dimensionIds := by
  simp [gridSetup,NatAssign.Instruction.Valid,dimensionIds]

theorem workBits_eq (Q N : ℕ) :
    waveWorkBits (8*Q) N=N+(waveDegree (8*Q) N).bits.length+32 := by
  have hc (K : ℕ) : Nat.clog 2 (K+1)=K.bits.length := by
    rw [Nat.size_eq_bits_len]
    apply Nat.le_antisymm
    · rw [Nat.clog_le_iff_le_pow (by decide)]
      exact Nat.succ_le_of_lt (Nat.lt_size_self K)
    · rw [Nat.size_le]
      have h := Nat.le_pow_clog (by decide : 1<(2:ℕ)) (K+1)
      omega
  rw [waveWorkBits,hc]

theorem degreeValues_eq (Q N i : ℕ) :
    degreeValues Q N i=if i=712 then waveDegree (8*Q) N else initialDimensions Q N i := by
  by_cases h712 : i=712
  · subst i
    simp [degreeValues,degreeSetup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initialDimensions,waveDegree]
    ring
  by_cases h717 : i=717
  · subst i
    simp [degreeValues,degreeSetup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initialDimensions]
  rw [ite_eq_right h712]
  exact RationalDataflow.values_unchanged degreeSetup (initialDimensions Q N) i (by
    simp [degreeSetup,NatAssign.Instruction.target,Ne.symm h712,Ne.symm h717])

theorem finalDimensions_work (Q N : ℕ) : finalDimensions Q N 714=waveWorkBits (8*Q) N := by
  simp [finalDimensions,gridSetup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,scannedValues,degreeValues_eq,
    initialDimensions,workBits_eq]
  omega

theorem finalDimensions_grid (Q N : ℕ) : finalDimensions Q N 715=waveGrid (8*Q) N := by
  simp [finalDimensions,gridSetup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,scannedValues,degreeValues_eq,
    initialDimensions,waveGrid,waveDegree,workBits_eq]
  ring

theorem finalDimensions_count (Q N : ℕ) : finalDimensions Q N 716=waveDegree (8*Q) N+1 := by
  simp [finalDimensions,gridSetup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,scannedValues,degreeValues_eq,
    initialDimensions]
  omega

theorem finalDimensions_eq (Q N i : ℕ) : finalDimensions Q N i=
    if i=714 then waveWorkBits (8*Q) N else if i=715 then waveGrid (8*Q) N else
      if i=716 then waveDegree (8*Q) N+1 else scannedValues Q N i := by
  by_cases h714 : i=714
  · subst i;simpa using finalDimensions_work Q N
  by_cases h715 : i=715
  · subst i;simpa using finalDimensions_grid Q N
  by_cases h716 : i=716
  · subst i;simpa using finalDimensions_count Q N
  by_cases h717 : i=717
  · subst i
    simp [finalDimensions,gridSetup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,scannedValues,degreeValues_eq,
      initialDimensions]
  simp [finalDimensions,gridSetup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,h714,h715,h716,h717]

#print axioms finalDimensions_eq
end Maxwell.Continuum.Profile.WaveMachine.Runtime
