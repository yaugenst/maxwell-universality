import Maxwell.Continuum.ProfileSampleEvaluation
import Maxwell.Continuum.NaturalBankStage
import Maxwell.Continuum.StoredWordLength

/-! The literal profile degree, work precision and DFT grid are computed
from a stored requested precision by one fixed instruction program. -/
namespace Maxwell.Continuum.Profile.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def dimensionIds : Finset ℕ := {660,661,662,663,664,665,666}
def dimensionWorkspace : Finset ℕ := {0,1,2,3}∪dimensionIds

def initialDimensions (N i : ℕ) : ℕ := if i=660 then N else 0

def degreeSetup : List NatAssign.Instruction :=
  [.copy 660 661,.literal 665 256,.add 665 661,.literal 665 128,.multiply 665 661,
   .copy 661 666,.multiply 666 661,.literal 665 0,.literal 666 0]
def degreeValues (N : ℕ) : ℕ→ℕ := NatAssign.values degreeSetup (initialDimensions N)
def scannedValues (N : ℕ) : ℕ→ℕ := Function.update (degreeValues N) 662 (profileDegree N).bits.length

def gridSetup : List NatAssign.Instruction :=
  [.copy 660 663,.copy 662 665,.literal 666 3,.multiply 666 665,.add 665 663,
   .literal 665 32,.add 665 663,.copy 663 664,.literal 665 256,.add 665 664,
   .literal 665 128,.multiply 665 664,.copy 664 666,.multiply 666 664,
   .add 661 664,.literal 665 1,.add 665 664,.literal 665 0,.literal 666 0]
def finalDimensions (N : ℕ) : ℕ→ℕ := NatAssign.values gridSetup (scannedValues N)
def dimensionCode : Code := .seq (NatAssign.code degreeSetup)
  (.seq (WordLength.code 661 662) (NatAssign.code gridSetup))

theorem dimensionIds_ge (i : ℕ) (hi : i∈dimensionIds) : 4 ≤ i := by
  simp only [dimensionIds,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem degreeSetup_valid : ∀a∈degreeSetup,a.Valid dimensionIds := by
  simp [degreeSetup,NatAssign.Instruction.Valid,dimensionIds]

theorem gridSetup_valid : ∀a∈gridSetup,a.Valid dimensionIds := by
  simp [gridSetup,NatAssign.Instruction.Valid,dimensionIds]

theorem workBits_eq (N : ℕ) : profileWorkBits N=N+3*(profileDegree N).bits.length+32 := by
  have hc (Q : ℕ) : Nat.clog 2 (Q+1)=Q.bits.length := by
    rw [Nat.size_eq_bits_len]
    apply Nat.le_antisymm
    · rw [Nat.clog_le_iff_le_pow (by decide)]
      exact Nat.succ_le_of_lt (Nat.lt_size_self Q)
    · rw [Nat.size_le]
      have h := Nat.le_pow_clog (by decide : 1<(2:ℕ)) (Q+1)
      omega
  rw [profileWorkBits,hc]

theorem degreeValues_eq (N i : ℕ) :
    degreeValues N i=if i=661 then profileDegree N else initialDimensions N i := by
  by_cases h661 : i=661
  · subst i
    simp [degreeValues,degreeSetup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initialDimensions,profileDegree,pow_two]
    ring
  by_cases h665 : i=665
  · subst i
    simp [degreeValues,degreeSetup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initialDimensions]
  by_cases h666 : i=666
  · subst i
    simp [degreeValues,degreeSetup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initialDimensions]
  rw [ite_eq_right h661]
  exact RationalDataflow.values_unchanged degreeSetup (initialDimensions N) i (by
    simp [degreeSetup,NatAssign.Instruction.target,Ne.symm h661,Ne.symm h665,Ne.symm h666])

theorem finalDimensions_work (N : ℕ) : finalDimensions N 663=profileWorkBits N := by
  simp [finalDimensions,gridSetup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,scannedValues,degreeValues_eq,
    initialDimensions,workBits_eq]
  omega

theorem finalDimensions_grid (N : ℕ) : finalDimensions N 664=profileGrid N := by
  simp [finalDimensions,gridSetup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,scannedValues,degreeValues_eq,
    initialDimensions,profileGrid,profileDegree,workBits_eq]
  ring

theorem finalDimensions_eq (N i : ℕ) : finalDimensions N i=
    if i=663 then profileWorkBits N else if i=664 then profileGrid N else scannedValues N i := by
  by_cases h663 : i=663
  · subst i;simpa using finalDimensions_work N
  by_cases h664 : i=664
  · subst i;simpa using finalDimensions_grid N
  by_cases h665 : i=665
  · subst i
    simp [finalDimensions,gridSetup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,scannedValues,degreeValues_eq,initialDimensions]
  by_cases h666 : i=666
  · subst i
    simp [finalDimensions,gridSetup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,scannedValues,degreeValues_eq,initialDimensions]
  simp [finalDimensions,gridSetup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,h663,h664,h665,h666]

#print axioms finalDimensions_eq
end Maxwell.Continuum.Profile.Runtime
