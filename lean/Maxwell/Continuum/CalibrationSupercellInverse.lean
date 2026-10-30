import Maxwell.Continuum.CalibrationCutoffGrid
import Maxwell.Continuum.CalibrationSupercellOperator

/-! The complete finite Bloch grid of rational inverse applications on
global supercell Fourier coefficients. The unitary regrouping preserves
the uniform local error, independently of the number of samples. -/

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber Auxiliary PeriodicBand

variable (M : ℕ) [NeZero M]

def gridCoordinates (j : Grid M) : Fin 3 → ℚ := fun i => centeredGrid M (j i)

def rationalApply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (z σ : ℚ) (K P : ℕ) (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  fun n i =>
    let p := (indexEquiv M).symm n
    rationalGridApply z σ (gridCoordinates M p.1) K P
      (fun ν k => f (join M (p.1,ν)) k) p.2 i

theorem rationalApply_join {V : Type*} [AddCommGroup V] [Module ℚ V]
    (z σ : ℚ) (K P : ℕ) (f : Alias → Fin 3 → V) (j : Grid M) (ν : Alias) (i : Fin 3) :
    rationalApply M z σ K P f (join M (j,ν)) i =
      rationalGridApply z σ (gridCoordinates M j) K P (fun μ k => f (join M (j,μ)) k) ν i := by
  unfold rationalApply
  change (let p := (indexEquiv M).symm ((indexEquiv M) (j,ν));
    rationalGridApply z σ (gridCoordinates M p.1) K P
      (fun μ k => f (join M (p.1,μ)) k) p.2 i) = _
  rw [Equiv.symm_apply_apply]

noncomputable section
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] fiberResolvent roundedGridFull PeriodicBand.scaledBand
  PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK CornerBridge.topState

def exactInverse (z σ : ℝ) : FiberSpace →L[ℂ] FiberSpace :=
  operator M (fun j => actualGridInverse z σ (gridCoordinates M j))

def roundedInverse {L : ℝ} (z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64) (K P : ℕ) :
    FiberSpace →L[ℂ] FiberSpace :=
  operator M (fun j => roundedGridInverse z σ D hσ0 hσ (gridCoordinates M j) K P)

theorem roundedInverse_error {L : ℝ} (hL : 1 ≤ L)
    (z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (N ell K P : ℕ) (hlog : L ≤ (2 : ℝ)^ell)
    (hK : aliasSteps (N+2) ell ≤ K) (hP : cutoffWorkBits N ell ≤ P) :
    ‖exactInverse M z σ-roundedInverse M z σ D hσ0 hσ K P‖ ≤ (1/2 : ℝ)^N := by
  apply operator_error M _ _ (by positivity)
  intro j
  exact roundedGridInverse_error hL z σ D hσ0 hσ (gridCoordinates M j) N ell K P hlog hK hP

theorem rationalApply_represents {L : ℝ} (hL : 1 ≤ L)
    (z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (N ell K P : ℕ) (hlog : L ≤ (2 : ℝ)^ell) (hK : aliasSteps N ell ≤ K)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalApply M z σ K P f) (roundedInverse M z σ D hσ0 hσ K P u) := by
  intro n i
  obtain ⟨⟨j,ν⟩,rfl⟩ := (indexEquiv M).surjective n
  change rationalComplexValue (rationalApply M z σ K P f (join M (j,ν)) i) =
    roundedInverse M z σ D hσ0 hσ K P u (join M (j,ν)) i
  rw [rationalApply_join]
  have hj : Represents (fun μ k => f (join M (j,μ)) k) (fiber M u j) := fun μ k => hf _ k
  have h := rationalGridApply_represents hL z σ D hσ0 hσ (gridCoordinates M j)
    N ell K P hlog hK hj
  rw [roundedInverse,operator_apply]
  exact h ν i

#print axioms roundedInverse_error
#print axioms rationalApply_represents

end
end Maxwell.Continuum.Calibration.Supercell
