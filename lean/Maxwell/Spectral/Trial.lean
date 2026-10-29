import Maxwell.Spectral.Coercivity
import Maxwell.Spectral.TaylorRemainder

/-!
# Operator remainder data imply the local spectral-polynomial bound

The hypotheses below are exact center/second-order forms and the explicit
remainder package constructed in `TaylorRemainder`. No coercivity or band
inequality is supplied as a hypothesis.
-/

namespace Maxwell.Spectral

noncomputable section

variable {H V : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem quadratic_remainder_bound (K : V →L[ℂ] V) (κ : ℝ) (hK : ‖K‖ ≤ κ)
    (x : V) : |Complex.re (inner ℂ x (K x))| ≤ κ * ‖x‖ ^ 2 := by
  have hx := (K.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hK (norm_nonneg x))
  calc
    _ ≤ ‖inner ℂ x (K x)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖K x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (κ * ‖x‖) := mul_le_mul_of_nonneg_left hx (norm_nonneg x)
    _ = _ := by ring

omit [CompleteSpace H] [CompleteSpace V] in
theorem corrected_trial_gram_bound (Φ : V →ₗᵢ[ℂ] H) (Y : V →L[ℂ] H)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20) (hY : ‖Y‖ ≤ 3 * r)
    (horth : ∀ x, inner ℂ (Φ x) (Y x) = 0) (x : V) :
    ‖Φ x - Y x‖ ^ 2 ≤ (409 / 400) * ‖x‖ ^ 2 := by
  have hYx := (Y.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hY (norm_nonneg x))
  have hsq := pow_le_pow_left₀ (norm_nonneg (Y x)) hYx 2
  have hr2 := (radius_power_bounds r hr0 hr).1
  have hmul := mul_le_mul_of_nonneg_right hr2 (sq_nonneg ‖x‖)
  rw [norm_sub_sq (𝕜 := ℂ), horth x, map_zero, Φ.norm_map]
  nlinarith only [hsq, hmul]

omit [CompleteSpace H] [CompleteSpace V] in
theorem corrected_trial_gram_bound_of_norm (Φ Y : V →L[ℂ] H)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20)
    (hΦ : ‖Φ‖ ≤ 1) (hY : ‖Y‖ ≤ 3 * r)
    (horth : ∀ x, inner ℂ (Φ x) (Y x) = 0) (x : V) :
    ‖(Φ - Y) x‖ ^ 2 ≤ (409 / 400) * ‖x‖ ^ 2 := by
  have hΦx := (Φ.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hΦ (norm_nonneg x))
  have hYx := (Y.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hY (norm_nonneg x))
  have hΦsq := pow_le_pow_left₀ (norm_nonneg (Φ x)) hΦx 2
  have hYsq := pow_le_pow_left₀ (norm_nonneg (Y x)) hYx 2
  have hr2 := (radius_power_bounds r hr0 hr).1
  have hmul := mul_le_mul_of_nonneg_right hr2 (sq_nonneg ‖x‖)
  rw [sub_apply, norm_sub_sq (𝕜 := ℂ), horth x, map_zero]
  nlinarith only [hΦsq, hYsq, hmul]

theorem operator_trial_coercivity
    (B : H →L[ℂ] H) (F D R Reven Rodd : V →L[ℂ] H)
    (T K Krem : V →L[ℂ] V) (r δ E : ℝ)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (2 : ℝ) ^ 20)
    (hElo : 239 / 25000 ≤ E) (hEhi : E ≤ 957 / 100000)
    (hcompressed : F.adjoint.comp (B.comp F) = T + K + Krem)
    (hresidual : B.comp F = D + R + Reven + Rodd)
    (horth : (D + R + Reven).adjoint.comp Rodd = 0)
    (hKrem : ‖Krem‖ ≤ (13 / 5) * r ^ 4)
    (hReven : ‖Reven‖ ≤ (2 / 25) * r ^ 4)
    (hRodd : ‖Rodd‖ ≤ (17 / 20) * r ^ 3)
    (hD : ‖D‖ ≤ δ)
    (hklo : ∀ x, r ^ 2 * ‖x‖ ^ 2 / 50 ≤ Complex.re (inner ℂ x (K x)))
    (hkhi : ∀ x, Complex.re (inner ℂ x (K x)) ≤ r ^ 2 * ‖x‖ ^ 2)
    (hR : ∀ x, ‖R x‖ ^ 2 ≤ (18 / 5) * r ^ 2 * Complex.re (inner ℂ x (K x)))
    (hcross : ∀ x, Complex.re (inner ℂ (D x) (R x)) ≤ δ * r ^ 2 * ‖x‖ ^ 2)
    (hcenter : ∀ x, ‖D x‖ ^ 2 ≤ (7 / 256 - E) * Complex.re (inner ℂ x (T x)))
    (x : V) :
    r ^ 2 * ‖x‖ ^ 2 / 20000 ≤
      (7 / 256 - E) * Complex.re (inner ℂ (F x) (B (F x))) - ‖B (F x)‖ ^ 2 := by
  have hcomp : inner ℂ (F x) (B (F x)) =
      inner ℂ x (T x) + inner ℂ x (K x) + inner ℂ x (Krem x) := by
    rw [← F.adjoint_inner_right]
    have hh := congrArg (fun L : V →L[ℂ] V => L x) hcompressed
    simpa only [ContinuousLinearMap.comp_apply, add_apply,
      inner_add_right] using congrArg (inner ℂ x) hh
  have htail := (abs_le.mp (quadratic_remainder_bound Krem ((13 / 5) * r ^ 4) hKrem x)).1
  have hf : Complex.re (inner ℂ x (T x)) + Complex.re (inner ℂ x (K x)) -
      (13 / 5) * r ^ 4 * ‖x‖ ^ 2 ≤ Complex.re (inner ℂ (F x) (B (F x))) := by
    rw [hcomp, Complex.add_re, Complex.add_re]
    linarith
  have hres : B (F x) = D x + R x + Reven x + Rodd x :=
    congrArg (fun L : V →L[ℂ] H => L x) hresidual
  have hzero : inner ℂ (D x + R x + Reven x) (Rodd x) = 0 := by
    have hh := congrArg (fun L : V →L[ℂ] V => L x) horth
    have hi := congrArg (inner ℂ x) hh
    simpa only [ContinuousLinearMap.comp_apply, zero_apply,
      ContinuousLinearMap.adjoint_inner_right, add_apply,
      inner_zero_right] using hi
  have hnorm : ‖B (F x)‖ ^ 2 = ‖D x + R x + Reven x‖ ^ 2 + ‖Rodd x‖ ^ 2 := by
    rw [hres]
    simpa only [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hzero
  rw [hnorm]
  have h := full_residual_coercivity r δ E ‖x‖
    (Complex.re (inner ℂ x (T x))) (Complex.re (inner ℂ x (K x)))
    (Complex.re (inner ℂ (F x) (B (F x)))) (D x) (R x) (Reven x) (Rodd x)
    hr0 hr hδ0 hδ hElo hEhi (norm_nonneg x) (hklo x) (hkhi x)
    ((D.le_opNorm x).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg x)))
    (hR x)
    ((Reven.le_opNorm x).trans (mul_le_mul_of_nonneg_right hReven (norm_nonneg x)))
    ((Rodd.le_opNorm x).trans (mul_le_mul_of_nonneg_right hRodd (norm_nonneg x)))
    (hcross x) (hcenter x) hf
  linarith

/-- The finite center and second-order premises, expressed in the genuine
Hilbert norm. Every field only involves `A₀,A₁,A₂,Φ,Y`; none refers to a
remainder, a neighborhood coercivity conclusion, or a displaced eigenvalue. -/
structure FiniteJetBounds (A : ℕ → H →L[ℂ] H) (Φ Y : V →L[ℂ] H)
    (r δ E : ℝ) : Prop where
  centerResidualNorm : ‖(A 0).comp Φ‖ ≤ δ
  compressedLower : ∀ x, r ^ 2 * ‖x‖ ^ 2 / 50 ≤ Complex.re (inner ℂ x
    ((Φ.adjoint.comp ((A 2).comp Φ) - Φ.adjoint.comp ((A 1).comp Y)) x))
  compressedUpper : ∀ x, Complex.re (inner ℂ x
    ((Φ.adjoint.comp ((A 2).comp Φ) - Φ.adjoint.comp ((A 1).comp Y)) x)) ≤ r ^ 2 * ‖x‖ ^ 2
  residualGram : ∀ x, ‖residualTaylorTerm A Φ Y 1 x‖ ^ 2 ≤ (18 / 5) * r ^ 2 *
    Complex.re (inner ℂ x
      ((Φ.adjoint.comp ((A 2).comp Φ) - Φ.adjoint.comp ((A 1).comp Y)) x))
  mixedOffset : ∀ x, Complex.re (inner ℂ ((A 0).comp Φ x)
    (residualTaylorTerm A Φ Y 1 x)) ≤ δ * r ^ 2 * ‖x‖ ^ 2
  centerPolynomial : ∀ x, ‖(A 0).comp Φ x‖ ^ 2 ≤ (7 / 256 - E) *
    Complex.re (inner ℂ x (Φ.adjoint.comp ((A 0).comp Φ) x))

/-- Combine the convergent operator series, inversion symmetry, finite jet
data and the full residual square into the required quadratic estimate. -/
theorem taylor_trial_coercivity
    (A : ℕ → H →L[ℂ] H) (B : H →L[ℂ] H) (hseries : HasSum A B)
    (Φ Y : V →L[ℂ] H) (r δ E : ℝ)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (2 : ℝ) ^ 20)
    (hElo : 239 / 25000 ≤ E) (hEhi : E ≤ 957 / 100000)
    (hΦnorm : ‖Φ‖ ≤ 1) (hYnorm : ‖Y‖ ≤ 3 * r)
    (hcoeff : ∀ j, 1 ≤ j → ‖A j‖ ≤ taylorCoefficientMajorant j * r ^ j)
    (hcancel : (A 0).comp Y = (A 1).comp Φ)
    (I : H ≃ₗᵢ[ℂ] H) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1)
    (hparity : TaylorParity I A) (hΦ : HasParity I σ Φ) (hY : HasParity I (-σ) Y)
    (hjet : FiniteJetBounds A Φ Y r δ E) (x : V) :
    r ^ 2 * ‖x‖ ^ 2 / 20000 ≤
      (7 / 256 - E) * Complex.re (inner ℂ ((Φ - Y) x) (B ((Φ - Y) x))) -
        ‖B ((Φ - Y) x)‖ ^ 2 := by
  obtain ⟨Krem, Reven, Rodd, hcomp, hres, hKrem, hReven, hRodd, horth⟩ :=
    local_taylor_decomposition A B hseries Φ Y r hr0 hr hΦnorm hYnorm hcoeff
      hcancel I σ hσ hparity hΦ hY
  exact operator_trial_coercivity B (Φ - Y) ((A 0).comp Φ)
    (residualTaylorTerm A Φ Y 1) Reven Rodd (Φ.adjoint.comp ((A 0).comp Φ))
    (Φ.adjoint.comp ((A 2).comp Φ) - Φ.adjoint.comp ((A 1).comp Y)) Krem r δ E
    hr0 hr hδ0 hδ hElo hEhi hcomp hres horth hKrem hReven hRodd
    hjet.centerResidualNorm hjet.compressedLower hjet.compressedUpper
    hjet.residualGram hjet.mixedOffset hjet.centerPolynomial x

/-- Full local analytic implication: finite center/jet data and a concrete
Taylor series force the band separation of the original selfadjoint
operator. The inertia premise concerns only the fixed eligible band. -/
theorem local_band_gap_from_taylor [FiniteDimensional ℂ H] [FiniteDimensional ℂ V]
    (L : H →ₗ[ℂ] H) (hL : L.IsSymmetric)
    (A : ℕ → H →L[ℂ] H) (B : H →L[ℂ] H) (hseries : HasSum A B)
    (Φ Y : V →L[ℂ] H) (r δ E : ℝ)
    (hshift : B.toLinearMap = L - (E : ℂ) • (LinearMap.id : H →ₗ[ℂ] H))
    (hr0 : 0 < r) (hr : r ≤ 1 / 20)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (2 : ℝ) ^ 20)
    (hElo : 239 / 25000 ≤ E) (hEhi : E ≤ 957 / 100000)
    (hΦnorm : ‖Φ‖ ≤ 1) (hYnorm : ‖Y‖ ≤ 3 * r)
    (hcoeff : ∀ j, 1 ≤ j → ‖A j‖ ≤ taylorCoefficientMajorant j * r ^ j)
    (hcancel : (A 0).comp Y = (A 1).comp Φ)
    (I : H ≃ₗᵢ[ℂ] H) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1)
    (hparity : TaylorParity I A) (hΦ : HasParity I σ Φ) (hY : HasParity I (-σ) Y)
    (hjet : FiniteJetBounds A Φ Y r δ E)
    (hdim : 2 ≤ Module.finrank ℂ V)
    (hinertia : (Finset.univ.filter fun i =>
      0 < hL.eigenvalues rfl i ∧ hL.eigenvalues rfl i < 7 / 256).card ≤ 2) :
    ∀ i : Fin (Module.finrank ℂ H),
      0 < hL.eigenvalues rfl i → hL.eigenvalues rfl i < 7 / 256 →
      r ^ 2 / 600 < hL.eigenvalues rfl i - E := by
  apply local_band_gap_of_trial_map hL E r hElo hEhi hr0 hinertia
    (Φ - Y).toLinearMap hdim
  · intro x
    rw [edgePolynomialMap_quadratic L hL E (7 / 256), ← hshift]
    have h := taylor_trial_coercivity A B hseries Φ Y r δ E hr0.le hr
      hδ0 hδ hElo hEhi hΦnorm hYnorm hcoeff hcancel I σ hσ hparity hΦ hY hjet x
    convert h using 1
    ring
  · intro x
    exact corrected_trial_gram_bound_of_norm Φ Y r hr0.le hr hΦnorm hYnorm
      (fun x => inner_zero_of_opposite_parity I σ hσ Φ Y hΦ hY x x) x

end
end Maxwell.Spectral
