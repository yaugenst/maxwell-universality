import Maxwell.Green.TransverseCoordinates
import Maxwell.Green.Saddle

/-! Complex coordinate transport of the actual denominator derivatives. -/

noncomputable section

open Filter
open scoped Topology

namespace Maxwell.Green

abbrev PrincipalCoordinates := (ℂ × ℂ) × ℂ

def momentumComplex (v : MomentumSpace) : Fin 3 → ℂ := fun j => (v j : ℂ)

def principalChart (normal e₁ e₂ : MomentumSpace) : PrincipalCoordinates →L[ℂ] (Fin 3 → ℂ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z j => z.1.1 * (e₁ j : ℂ) + z.1.2 * (e₂ j : ℂ) + z.2 * (normal j : ℂ)
    map_add' := by intro x y; ext j; simp; ring
    map_smul' := by intro c x; ext j; simp; ring }

@[simp] theorem principalChart_apply (normal e₁ e₂ : MomentumSpace) (z : PrincipalCoordinates)
    (j : Fin 3) :
    principalChart normal e₁ e₂ z j = z.1.1 * (e₁ j : ℂ) + z.1.2 * (e₂ j : ℂ) +
      z.2 * (normal j : ℂ) := rfl

@[simp] theorem principalChart_normal (normal e₁ e₂ : MomentumSpace) :
    principalChart normal e₁ e₂ (0, 1) = momentumComplex normal := by
  ext j
  simp [momentumComplex]

theorem principalChart_realTransverse (normal e₁ e₂ : MomentumSpace) (w : ℂ) :
    principalChart normal e₁ e₂ (realTransverse w, 0) =
      momentumComplex (w.re • e₁ + w.im • e₂) := by
  ext j
  simp [realTransverse, momentumComplex]

theorem principalChart_vectors (normal e₁ e₂ : MomentumSpace) (z : PrincipalCoordinates) :
    principalChart normal e₁ e₂ z = z.1.1 • momentumComplex e₁ + z.1.2 • momentumComplex e₂ +
      z.2 • momentumComplex normal := by
  ext j
  rfl

section AffineDerivative

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

def affineDenominator (lam : E → ℂ) (center : E) (T : W →L[ℂ] E) (energy : ℂ) : W → ℂ :=
  fun z => lam (center + T z) - energy

theorem affineDenominator_analytic {lam : E → ℂ} {center : E}
    (hlam : AnalyticAt ℂ lam center) (T : W →L[ℂ] E) (energy : ℂ) :
    AnalyticAt ℂ (affineDenominator lam center T energy) 0 := by
  have ht : AnalyticAt ℂ (fun z => center + T z) 0 := analyticAt_const.add (T.analyticAt 0)
  exact (hlam.comp_of_eq ht (by simp)).sub analyticAt_const

theorem affineDenominator_fderiv {lam : E → ℂ} {center : E}
    (hlam : AnalyticAt ℂ lam center) (T : W →L[ℂ] E) (energy : ℂ) :
    fderiv ℂ (affineDenominator lam center T energy) 0 = (fderiv ℂ lam center).comp T := by
  have ht : HasFDerivAt (fun z => center + T z) T 0 := by
    simpa using T.hasFDerivAt.const_add center
  have hl : HasFDerivAt lam (fderiv ℂ lam center) (center + T 0) := by
    simpa using hlam.differentiableAt.hasFDerivAt
  exact ((hl.comp 0 ht).sub_const energy).fderiv

theorem affineDenominator_second {lam : E → ℂ} {center : E}
    (hlam : AnalyticAt ℂ lam center) (T : W →L[ℂ] E) (energy : ℂ) (x y : W) :
    (fderiv ℂ (fderiv ℂ (affineDenominator lam center T energy)) 0) x y =
      (fderiv ℂ (fderiv ℂ lam) center) (T x) (T y) := by
  let F := affineDenominator lam center T energy
  have ht : HasFDerivAt (fun z => center + T z) T 0 := by
    simpa using T.hasFDerivAt.const_add center
  have hnear : ∀ᶠ z in 𝓝 (0 : W), AnalyticAt ℂ lam (center + T z) := by
    apply ht.continuousAt.tendsto.eventually
    simpa using hlam.eventually_analyticAt
  have heq : (fun z => (fderiv ℂ F z) y) =ᶠ[𝓝 (0 : W)]
      (fun z => (fderiv ℂ lam (center + T z)) (T y)) := by
    filter_upwards [hnear] with z hz
    have hc := (hz.differentiableAt.hasFDerivAt.comp z
      (T.hasFDerivAt.const_add center)).sub_const energy
    have hf := congrArg (fun L : W →L[ℂ] ℂ => L y) hc.fderiv
    exact hf
  have hF := (affineDenominator_analytic hlam T energy).fderiv.differentiableAt.hasFDerivAt
    |>.clm_apply (hasFDerivAt_const y (0 : W))
  have hL : HasFDerivAt (fun z => fderiv ℂ lam (center + T z))
      ((fderiv ℂ (fderiv ℂ lam) center).comp T) 0 := by
    have hl : HasFDerivAt (fderiv ℂ lam) (fderiv ℂ (fderiv ℂ lam) center) (center + T 0) := by
      simpa using hlam.fderiv.differentiableAt.hasFDerivAt
    exact hl.comp 0 ht
  have hR := hL.clm_apply (hasFDerivAt_const (T y) (0 : W))
  have hd := hF.fderiv.symm.trans (heq.fderiv_eq.trans hR.fderiv)
  have hx := congrArg (fun L : W →L[ℂ] ℂ => L x) hd
  simpa [F] using hx

end AffineDerivative

/-- Support-gradient and Hessian identities in the original coordinates
produce all of the principal-coordinate jet inputs used by the saddle
construction. The transverse diagonalizer is constructed, not assumed. -/
theorem exists_principal_saddle_jet
    (lam : (Fin 3 → ℂ) → ℂ) (center : Fin 3 → ℂ) (energy : ℂ)
    (hlam : AnalyticAt ℂ lam center) (v : MomentumSpace) (hv : v ≠ 0)
    (χ : ℝ) (hχ : 0 < χ)
    (B : MomentumSpace →L[ℝ] MomentumSpace →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (hpos : ∀ x, x ≠ 0 → 0 < B x x)
    (hgradient : ∀ x : MomentumSpace,
      (fderiv ℂ lam center) (momentumComplex x) = Complex.I * (inner ℝ (χ • v) x : ℂ))
    (hHessian : ∀ x : MomentumSpace,
      (fderiv ℂ (fderiv ℂ lam) center) (momentumComplex x) (momentumComplex x) = (B x x : ℂ)) :
    ∃ (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (q : Fin 2 → ℝ),
      (∀ i, 0 < q i) ∧
      let T := principalChart (propagationNormal v) (b 0) (b 1)
      let F := affineDenominator lam center T energy
      AnalyticAt ℂ F 0 ∧
      (fderiv ℂ F 0) (0, 1) = Complex.I * ((χ * ‖v‖ : ℝ) : ℂ) ∧
      (fderiv ℂ F 0).comp (ContinuousLinearMap.inl ℂ (ℂ × ℂ) ℂ) = 0 ∧
      (∀ w : ℂ, -(2 : ℂ)⁻¹ * ((fderiv ℂ F 0) (0, 1))⁻¹ *
        (fderiv ℂ (fderiv ℂ F) 0) (realTransverse w, 0) (realTransverse w, 0) =
          quadraticPhase (χ * ‖v‖) (q 0) (q 1) w) := by
  obtain ⟨b, q, hq, hdiag⟩ := exists_transverse_principal_basis v hv B hB hpos
  refine ⟨b, q, hq, ?_⟩
  dsimp only
  let T := principalChart (propagationNormal v) (b 0) (b 1)
  let F := affineDenominator lam center T energy
  change AnalyticAt ℂ F 0 ∧ _
  have hfirst : fderiv ℂ F 0 = (fderiv ℂ lam center).comp T :=
    affineDenominator_fderiv hlam T energy
  have hnormal : (fderiv ℂ F 0) (0, 1) = Complex.I * ((χ * ‖v‖ : ℝ) : ℂ) := by
    rw [hfirst]
    change (fderiv ℂ lam center) (T (0, 1)) = _
    rw [principalChart_normal, hgradient, supportGradient_normal v hv]
  refine ⟨affineDenominator_analytic hlam T energy, hnormal, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro z
    rw [hfirst]
    change (fderiv ℂ lam center) (T (z, 0)) = 0
    rw [principalChart_vectors]
    simp [hgradient, supportGradient_transverse]
  · intro w
    rw [hnormal, affineDenominator_second hlam T energy,
      principalChart_realTransverse, hHessian,
      transverse_quadratic_diagonal v B b q hdiag]
    have hc : ((χ * ‖v‖ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos hχ (norm_pos_iff.mpr hv)).ne'
    unfold quadraticPhase
    push_cast
    field_simp
    simp [Complex.I_sq]
    ring

end Maxwell.Green
