import Maxwell.Continuum.CalibrationSupercellBounds
import Maxwell.Continuum.CalibrationRationalConvolution
import Maxwell.Continuum.CalibrationSupercellSupport
import Maxwell.Continuum.CalibrationSandwichEstimate

/-! The finite rational root-inverse-root application on the complete
supercell Fourier space. Each approximation is measured in operator
norm before composition; no Fourier-frequency truncation is assumed. -/

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber

variable (M : ℕ) [NeZero M]

def rationalSandwichApply (s z σ : ℚ) (W ell K P : ℕ) (f : RationalAliasField) : RationalAliasField :=
  rationalRootApply s W ell (rationalApply M z σ K P (rationalRootApply s W ell f))

theorem rationalSandwichApply_supported {f : RationalAliasField} {R : ℕ}
    (hf : RationalSupported f R) (s z σ : ℚ) (W ell K P : ℕ) :
    RationalSupported (rationalSandwichApply M s z σ W ell K P f)
      (R+2*rootDegree s W ell+M*(K+6)) := by
  have h := (rationalApply_supported M (hf.rootApply s W ell) z σ K P).rootApply s W ell
  convert! h using 1
  unfold outputRadius
  omega

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

attribute [local irreducible] Auxiliary.fiberResolvent roundedGridFull roundedInverse exactInverse
  PeriodicBand.scaledBand PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK CornerBridge.topState

def exactSandwich (s : ℝ) (hs : 4 ≤ s) (z σ : ℝ) : FiberSpace →L[ℂ] FiberSpace :=
  aliasMultiplier (rootTorus s hs)*exactInverse M z σ*aliasMultiplier (rootTorus s hs)

def roundedSandwich {L : ℝ} (s z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64) (W ell K P : ℕ) :
    FiberSpace →L[ℂ] FiberSpace :=
  computedRootConvolution s W ell*roundedInverse M z σ D hσ0 hσ K P*computedRootConvolution s W ell

theorem roundedSandwich_error {L : ℝ} (hL : 1 ≤ L) (s z σ : ℚ)
    (hs : 4 ≤ (s : ℝ)) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (W ellRoot ellLength K P : ℕ) (hslog : (s : ℝ) ≤ (2 : ℝ)^ellRoot)
    (hLlog : L ≤ (2 : ℝ)^ellLength)
    (hK : aliasSteps (W+2) ellLength ≤ K) (hP : cutoffWorkBits W ellLength ≤ P) :
    ‖exactSandwich M s hs z σ-roundedSandwich M s z σ D hσ0 hσ W ellRoot K P‖ ≤
      (14*L^2+2)*(1/2 : ℝ)^W := by
  let Q := aliasMultiplier (rootTorus s hs)
  let Qb := computedRootConvolution s W ellRoot
  let R := exactInverse M z σ
  let Rb := roundedInverse M z σ D hσ0 hσ K P
  have hQ : ‖Q‖ ≤ 1 := (aliasMultiplier_norm _).trans
    ((ContinuousMap.norm_le _ zero_le_one).mpr (rootTorus_norm_le_one s hs))
  have hQb : ‖Qb‖ ≤ 2 := computedRootConvolution_norm s hs W ellRoot hslog
  have hQe : ‖Q-Qb‖ ≤ (1/2 : ℝ)^W := computedRootConvolution_error s hs W ellRoot hslog
  have hR : ‖R‖ ≤ 4*L^2 := exactInverse_norm M D hσ0 hσ
  have hRb : ‖Rb‖ ≤ 5*L^2 := roundedInverse_norm M hL z σ D hσ0 hσ W ellLength K P hLlog hK hP
  have hRe : ‖R-Rb‖ ≤ (1/2 : ℝ)^W := roundedInverse_error M hL z σ D hσ0 hσ
    W ellLength K P hLlog hK hP
  exact sandwich_difference_norm Q Qb R Rb hQ hQb hQe hR hRb hRe

theorem rationalSandwichApply_represents {L : ℝ} (hL : 1 ≤ L)
    (s z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (N ellLength W ellRoot K P : ℕ) (hlog : L ≤ (2 : ℝ)^ellLength)
    (hK : aliasSteps N ellLength ≤ K)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalSandwichApply M s z σ W ellRoot K P f)
      (roundedSandwich M s z σ D hσ0 hσ W ellRoot K P u) :=
  rationalRootApply_represents s W ellRoot
    (rationalApply_represents M hL z σ D hσ0 hσ N ellLength K P hlog hK
      (rationalRootApply_represents s W ellRoot hf))

#print axioms roundedSandwich_error
#print axioms rationalSandwichApply_represents

end
end Maxwell.Continuum.Calibration.Supercell
