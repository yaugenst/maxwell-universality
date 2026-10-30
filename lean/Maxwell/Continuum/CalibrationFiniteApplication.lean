import Maxwell.Continuum.CalibrationFiniteData
import Maxwell.Continuum.CalibrationSupercellArray
import Maxwell.Continuum.CalibrationSandwich

/-! The actual finite-array application used in calibration. Each
intermediate Fourier vector is materialized, including all sampled
inverse blocks, before it is reused by the next stage. -/

namespace Maxwell.Continuum.Calibration.FourierData

open FreeFiber Supercell

attribute [local irreducible] rootDegree

def rootApply (s : ℚ) (W ell : ℕ) (v : FourierData) : FourierData :=
  ofSupported (rationalRootApply s W ell v.field) (v.radius+rootDegree s W ell)

theorem rootApply_value (s : ℚ) (W ell : ℕ) (v : FourierData) :
    (rootApply s W ell v).value = computedRootConvolution s W ell v.value :=
  ofSupported_value (v.supported.rootApply s W ell) (rationalRootApply_represents s W ell v.represents)

def inverseApply (M : ℕ) [NeZero M] (z σ : ℚ) (K P : ℕ) (v : FourierData) : FourierData :=
  ⟨outputRadius M v.radius K,cachedApply M z σ v.radius K P v.field⟩

theorem inverseApply_field (M : ℕ) [NeZero M] (z σ : ℚ) (K P : ℕ) (v : FourierData) :
    (inverseApply M z σ K P v).field = rationalApply M z σ K P v.field :=
  cachedApply_eq M z σ v.radius K P v.supported

theorem inverseApply_value (M : ℕ) [NeZero M] {L : ℝ} (hL : 1 ≤ L)
    (z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (N ell K P : ℕ) (hlog : L ≤ (2 : ℝ)^ell) (hK : aliasSteps N ell ≤ K) (v : FourierData) :
    (inverseApply M z σ K P v).value = roundedInverse M z σ D hσ0 hσ K P v.value := by
  apply represents_unique (inverseApply M z σ K P v).represents
  rw [inverseApply_field]
  exact rationalApply_represents M hL z σ D hσ0 hσ N ell K P hlog hK v.represents

def sandwichApply (M : ℕ) [NeZero M] (s z σ : ℚ) (W ell K P : ℕ) (v : FourierData) : FourierData :=
  rootApply s W ell (inverseApply M z σ K P (rootApply s W ell v))

theorem sandwichApply_radius (M : ℕ) [NeZero M] (s z σ : ℚ) (W ell K P : ℕ) (v : FourierData) :
    (sandwichApply M s z σ W ell K P v).radius = v.radius+2*rootDegree s W ell+M*(K+6) := by
  change (v.radius+rootDegree s W ell+M*(K+6))+rootDegree s W ell = _
  omega

theorem sandwichApply_value (M : ℕ) [NeZero M] {L : ℝ} (hL : 1 ≤ L)
    (s z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (N ellLength W ellRoot K P : ℕ) (hlog : L ≤ (2 : ℝ)^ellLength)
    (hK : aliasSteps N ellLength ≤ K) (v : FourierData) :
    (sandwichApply M s z σ W ellRoot K P v).value =
      roundedSandwich M s z σ D hσ0 hσ W ellRoot K P v.value := by
  rw [sandwichApply,rootApply_value,inverseApply_value M hL z σ D hσ0 hσ N ellLength K P hlog hK,
    rootApply_value]
  rfl

def iterate (M : ℕ) [NeZero M] (c s z σ : ℚ) (W ell K P : ℕ) (v : FourierData) : ℕ → FourierData
  | 0 => v
  | n+1 => scale c (sandwichApply M s z σ W ell K P (iterate M c s z σ W ell K P v n))

private theorem affine_radius (r : ℕ → ℕ) (a d : ℕ) (h0 : r 0 = a)
    (hs : ∀ n, r (n+1) = r n+d) (n : ℕ) : r n = a+n*d := by
  induction n with
  | zero => simpa only [Nat.zero_mul,Nat.add_zero] using h0
  | succ n ih => rw [hs,ih]; ring

theorem scale_radius (c : ℚ) (v : FourierData) : (scale c v).radius = v.radius := rfl

theorem iterate_radius (M : ℕ) [NeZero M] (c s z σ : ℚ) (W ell K P : ℕ) (v : FourierData) (n : ℕ) :
    (iterate M c s z σ W ell K P v n).radius =
      v.radius+n*(2*rootDegree s W ell+M*(K+6)) := by
  apply affine_radius (fun n => (iterate M c s z σ W ell K P v n).radius)
  · rfl
  · intro k
    rw [iterate,scale_radius,sandwichApply_radius]
    exact Nat.add_assoc _ _ _

theorem iterate_value (M : ℕ) [NeZero M] {L : ℝ} (hL : 1 ≤ L)
    (c s z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (N ellLength W ellRoot K P : ℕ) (hlog : L ≤ (2 : ℝ)^ellLength)
    (hK : aliasSteps N ellLength ≤ K) (v : FourierData) (n : ℕ) :
    (iterate M c s z σ W ellRoot K P v n).value =
      (((c : ℂ) • roundedSandwich M s z σ D hσ0 hσ W ellRoot K P)^n) v.value := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate,scale_value,sandwichApply_value M hL s z σ D hσ0 hσ N ellLength W ellRoot K P hlog hK,
      ih,pow_succ']
    rfl

#print axioms sandwichApply_value
#print axioms iterate_value

end Maxwell.Continuum.Calibration.FourierData
