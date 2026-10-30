import Maxwell.Continuum.CalibrationFullApprox

/-! Applying the finite inverse formula to finite Fourier data uses
only finitely many aliases, with the manuscript's explicit radius. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

open FreeFiber

theorem AliasSupported.sub {u v : FiberSpace} {R : ℕ}
    (hu : AliasSupported u R) (hv : AliasSupported v R) : AliasSupported (u-v) R := by
  intro ν hν
  change u ν-v ν = 0
  rw [hu ν hν,hv ν hν,sub_self]

theorem extendCentral_supported (J : centralSpace →L[ℂ] centralSpace) (u : FiberSpace) :
    AliasSupported (extendCentral J u) 1 := by
  have h : centralAliasProjection (extendCentral J u) = extendCentral J u :=
    (mem_centralSpace_iff _).mp (J (centralProjectionToSpace u)).property
  rw [← h]
  exact centralAliasProjection_supported _

variable (t : Momentum) (e : ℂ)
variable (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8)

theorem calibrationComplementApprox_supported {u : FiberSpace} {R : ℕ}
    (hu : AliasSupported u R) (K : ℕ) :
    AliasSupported (calibrationComplementApprox t e ht he K u) (R+K) :=
  calibrationInverseApprox_supported hu.noncentralProjection t e ht he K

theorem calibrationLiftApprox_supported (u : FiberSpace) (K : ℕ) :
    AliasSupported (calibrationLiftApprox t e ht he K u) (K+2) := by
  exact ((centralAliasProjection_supported u).mono (by omega)).sub
    (calibrationSchurApprox_alias_radius t e ht he K u)

theorem calibrationFullApprox_supported {u : FiberSpace} {R : ℕ}
    (hu : AliasSupported u R) (K : ℕ) :
    AliasSupported (calibrationFullApprox t e ht he K u) (R+2*K+4) := by
  exact ((calibrationComplementApprox_supported t e ht he hu K).mono (by omega)).add
    ((calibrationLiftApprox_supported t e ht he _ K).mono (by omega))

theorem calibrationFullApprox_finite_support {u : FiberSpace} {R : ℕ}
    (hu : AliasSupported u R) (K : ℕ) :
    (Function.support (calibrationFullApprox t e ht he K u : Alias → Polarization)).Finite :=
  (calibrationFullApprox_supported t e ht he hu K).finite_support

#print axioms calibrationFullApprox_supported
#print axioms calibrationFullApprox_finite_support

end Maxwell.Continuum.Calibration
