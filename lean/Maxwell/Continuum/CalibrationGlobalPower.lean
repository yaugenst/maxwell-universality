import Maxwell.Continuum.CalibrationGlobalCoordinates
import Maxwell.Continuum.CalibrationPowerChannels
import Maxwell.Continuum.CalibrationFiniteAlgorithm
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! One fixed finite rational matrix reproduces every actual Fourier power
up to the requested iteration count. The final support cube contains all
intermediate fields, so no truncation or projection error is assumed. -/

namespace Maxwell.Continuum.Calibration.GlobalPower
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def finiteLinear (R : ℕ) (T : RationalAliasField →ₗ[ℚ] RationalAliasField) :
    (Fin (2*aliasArraySize R)→ℚ) →ₗ[ℚ] (Fin (2*aliasArraySize R)→ℚ) :=
  (sampleLinear R).comp (T.comp (embedLinear R))

def matrix (R : ℕ) (T : RationalAliasField →ₗ[ℚ] RationalAliasField) :
    Matrix (Fin (2*aliasArraySize R)) (Fin (2*aliasArraySize R)) ℚ :=
  fun i j => sample R (T (embed R (Pi.single j 1))) i

theorem matrix_mulVec (R : ℕ) (T : RationalAliasField →ₗ[ℚ] RationalAliasField)
    (x : Fin (2*aliasArraySize R)→ℚ) :
    (matrix R T).mulVec x=sample R (T (embed R x)) :=
  LinearMap.toMatrix'_mulVec (finiteLinear R T) x

theorem matrix_on_supported (R : ℕ) (T : RationalAliasField →ₗ[ℚ] RationalAliasField)
    (f : RationalAliasField) (hf : RationalSupported f R) :
    (matrix R T).mulVec (sample R f)=sample R (T f) := by
  rw [matrix_mulVec,embed_sample hf]

def finalRadius (M : ℕ) (s : ℚ) (W ell K : ℕ) (v : FourierData) (N : ℕ) : ℕ :=
  v.radius+N*(2*rootDegree s W ell+M*(K+6))

theorem iterate_supported_final (M : ℕ) [NeZero M] (c s z σ : ℚ)
    (W ell K P : ℕ) (v : FourierData) (N k : ℕ) (hk : k≤N) :
    RationalSupported (FourierData.iterate M c s z σ W ell K P v k).field
      (finalRadius M s W ell K v N) := by
  apply (FourierData.iterate M c s z σ W ell K P v k).supported.mono
  rw [FourierData.iterate_radius]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _

theorem powers_equal_samples (M : ℕ) [NeZero M] (c s z σ : ℚ)
    (W ell K P : ℕ) (v : FourierData) (N k : ℕ) (hk : k≤N) :
    PowerMachine.rationalPower
      (matrix (finalRadius M s W ell K v N) (stepLinear M c s z σ W ell K P))
      (sample (finalRadius M s W ell K v N) v.field) k=
    sample (finalRadius M s W ell K v N)
      (FourierData.iterate M c s z σ W ell K P v k).field := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [PowerMachine.rationalPower,ih (by omega),matrix_on_supported _ _ _
      (iterate_supported_final M c s z σ W ell K P v N k (by omega)),stepLinear_field]
    rfl

theorem powers_equal_fields (M : ℕ) [NeZero M] (c s z σ : ℚ)
    (W ell K P : ℕ) (v : FourierData) (N k : ℕ) (hk : k≤N) :
    embed (finalRadius M s W ell K v N)
      (PowerMachine.rationalPower
        (matrix (finalRadius M s W ell K v N) (stepLinear M c s z σ W ell K P))
        (sample (finalRadius M s W ell K v N) v.field) k)=
      (FourierData.iterate M c s z σ W ell K P v k).field := by
  rw [powers_equal_samples M c s z σ W ell K P v N k hk]
  exact embed_sample (iterate_supported_final M c s z σ W ell K P v N k hk)

def modeRadius (L r N : ℕ) : ℕ :=
  finalRadius (FiniteAlgorithm.size L r N) (FiniteAlgorithm.scale L r N)
    (FiniteAlgorithm.precision L r N) (FiniteAlgorithm.rootBits L r N)
    (FiniteAlgorithm.inverseSteps L r N) (FiniteAlgorithm.seed L r N) (FiniteAlgorithm.iterations N)

def modeMatrix (L r N : ℕ) (z : ℚ) :
    Matrix (Fin (2*aliasArraySize (modeRadius L r N))) (Fin (2*aliasArraySize (modeRadius L r N))) ℚ :=
  matrix (modeRadius L r N)
    (stepLinear (FiniteAlgorithm.size L r N) (FiniteAlgorithm.operatorScale L)
      (FiniteAlgorithm.scale L r N) z 0 (FiniteAlgorithm.precision L r N)
      (FiniteAlgorithm.rootBits L r N) (FiniteAlgorithm.inverseSteps L r N)
      (FiniteAlgorithm.cutoffBits L r N))

theorem rawMode_fixed_matrix (L r N : ℕ) (z : ℚ) :
    embed (modeRadius L r N)
      (PowerMachine.rationalPower (modeMatrix L r N z)
        (sample (modeRadius L r N) (FiniteAlgorithm.seed L r N).field) (FiniteAlgorithm.iterations N))=
      (FiniteAlgorithm.rawMode L r N z).field :=
  powers_equal_fields _ _ _ _ _ _ _ _ _ _ _ _ le_rfl

#print axioms matrix_mulVec
#print axioms powers_equal_fields
#print axioms rawMode_fixed_matrix

end Maxwell.Continuum.Calibration.GlobalPower
