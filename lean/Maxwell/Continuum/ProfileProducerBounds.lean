import Maxwell.Continuum.ProfileInitializedTable

/-! One explicit polynomial working-word budget discharges all precision
and transform-width premises of the computed profile table. -/
namespace Maxwell.Continuum.Profile.Runtime
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

def workingBudget (U : ℕ) : ℕ := 2^500*(U+1)^18
def runtimeBudget (N : ℕ) : ℕ := workingBudget (producerSize N)

theorem workingBudget_base (U : ℕ) : U+1≤workingBudget U := by
  have hp : U+1≤(U+1)^18 := Nat.le_self_pow (by decide) _
  unfold workingBudget
  exact hp.trans (Nat.le_mul_of_pos_left _ (by norm_num))

theorem roundedWidth_mono_grid (g G U : ℕ) (h : g≤G) : roundedWidth g U≤roundedWidth G U := by
  have hm := Nat.mul_le_mul_right (dftTermWidth U+1) (Nat.add_le_add_right h 1)
  unfold roundedWidth cosineWidth dftNormalizationWidth dftLoopWidth
  omega

theorem roundedWidth_diagonal_bound (U : ℕ) : roundedWidth U U≤2^450*(U+1)^18 := by
  simp only [roundedWidth,cosineWidth,dftNormalizationWidth,dftLoopWidth,dftScratchWidth,
    roundedRawWidth,sampledRawWidth,dftRawWidth,dftTermWidth,angularRawWidth,angularPhaseWidth,dftPhaseWidth]
  ring_nf
  omega

theorem roundedWidth_workingBudget (grid U : ℕ) (hg : grid≤U) : roundedWidth grid U≤workingBudget U := by
  apply ((roundedWidth_mono_grid grid U U hg).trans (roundedWidth_diagonal_bound U)).trans
  exact Nat.mul_le_mul_right _ (by norm_num)

theorem roundedWidth_components (grid U : ℕ) :
    dftLoopWidth grid U≤roundedWidth grid U ∧
    dftNormalizationWidth grid U≤roundedWidth grid U ∧
    cosineWidth grid U≤roundedWidth grid U ∧ dftRawWidth U≤roundedWidth grid U := by
  unfold roundedWidth cosineWidth dftNormalizationWidth
  omega

theorem runtimeBudget_parameters (N : ℕ) :
    1≤runtimeBudget N ∧ roundedWidth (profileGrid N) (producerSize N)≤runtimeBudget N ∧
    (profileDegree N).bits.length≤runtimeBudget N ∧
    ((2:ℕ)^profileWorkBits N).bits.length≤runtimeBudget N ∧
    N.bits.length≤runtimeBudget N := by
  obtain ⟨_,hg,hD,hP⟩ := producerSize_bounds N
  have base := workingBudget_base (producerSize N)
  have hn : N≤producerSize N := by
    have hp : N+1≤(N+1)^2 := Nat.le_self_pow (by decide) _
    unfold producerSize
    omega
  refine ⟨(Nat.succ_pos _).trans_le base,roundedWidth_workingBudget _ _ hg,
    (bits_le_of_le hD).trans base,?_,(bits_le_of_le hn).trans base⟩
  rw [Nat.size_eq_bits_len,Nat.size_pow]
  exact (Nat.add_le_add_right hP 1).trans base

theorem runtimeBudget_polynomial (N : ℕ) : runtimeBudget N≤2^1400*(N+1)^36 := by
  have hp : 1≤(N+1)^2 := one_le_pow₀ (by omega)
  have hsize : producerSize N+1≤2^47*(N+1)^2 := by unfold producerSize;omega
  calc
    runtimeBudget N≤2^500*(2^47*(N+1)^2)^18 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 18)
    _=2^1346*(N+1)^36 := by ring
    _≤_ := Nat.mul_le_mul_right _ (by norm_num)

#print axioms runtimeBudget_parameters
#print axioms runtimeBudget_polynomial
end Maxwell.Continuum.Profile.Runtime
