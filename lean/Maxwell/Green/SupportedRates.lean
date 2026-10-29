import Maxwell.Green.SpectralLevelBody
import Maxwell.Green.RateGeometry

/-! The actual spectral body and a single rounded integer placement share
strictly separated global and axial decay exponents. -/

noncomputable section
namespace Maxwell.Green
open Filter Metric Set Matrix
open scoped Topology InnerProductSpace ContDiff Matrix.Norms.L2Operator
set_option maxHeartbeats 800000

namespace SpectralLevelBodyData
variable {lam : ComplexTorusCoordinates → ℂ} {edge : ℝ}

/-- The same body used for the saddle has uniform inner and outer Hessian
ellipsoids. Its outer bound uses the proved coercivity to stay inside the
Taylor chart, even if the original body chart is larger. -/
theorem exists_whitened_level_geometry (D : SpectralLevelBodyData lam edge)
    {η : ℝ} (hη : 0 < η) :
    ∃ (Q P : Mat3) (M : ℕ) (ξ₀ : ℝ), 0 < M ∧ 0 < ξ₀ ∧
      P * Q = 1 ∧ Q * P = 1 ∧
      (∀ x y : Vec3, inner ℝ (matrixAction P x) y = inner ℝ x (matrixAction P y)) ∧
      IsUnit (roundedPlacementReal M Q) ∧
      (∀ x : Vec3, ‖matrixAction (P * roundedPlacementReal M Q) x‖ ≤
        (M : ℝ) * (1 + (1 : ℝ) / 100) * ‖x‖) ∧
      (∀ n : Fin 3 → ℤ,
        (M : ℝ) * (1 - (1 : ℝ) / 100) / Real.sqrt 3 *
          (∑ j : Fin 3, |(n j : ℝ)|) ≤
          ‖matrixAction P (integerMomentum (roundedPlacement M Q *ᵥ n))‖) ∧
      ∀ ξ : ℝ, 0 < ξ → ξ < ξ₀ →
        (∀ β : MomentumSpace,
          ‖matrixAction Q β‖ ≤ (1 - (1 : ℝ) / 100) * Real.sqrt (2 * ξ) →
          ‖β‖ < η ∧ β ∈ ball (0 : MomentumSpace) D.radius ∧
            imaginaryMomentumLevel lam edge β < ξ) ∧
        (∀ β ∈ D.body ξ,
          ‖matrixAction Q β‖ ≤ (1 + (1 : ℝ) / 100) * Real.sqrt (2 * ξ)) := by
  have hzero : Complex.I • momentumComplex (0 : MomentumSpace) = 0 := by
    ext j
    simp [momentumComplex]
  have hA : AnalyticAt ℂ lam 0 := by
    simpa only [hzero] using D.local_analytic 0 (mem_closedBall_self D.radius_pos.le)
  have hpos : ∀ x : MomentumSpace, x ≠ 0 → 0 < momentumHessian lam 0 x x := by
    intro x hx
    have h := D.hessian_lower 0 (mem_closedBall_self D.radius_pos.le) x
    rw [hzero] at h
    exact (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) D.quadraticConstant_pos)
      (sq_pos_of_pos (norm_pos_iff.mpr hx))).trans_le h
  obtain ⟨Q, P, M, hM, hPQ, hQP, _, hsym, hmetric, hunit, hdist, hl1⟩ :=
    exists_whitened_integer_placement (momentumHessian lam 0)
      (momentumHessian_symmetric lam 0 hA) hpos
  have hF : ContDiffAt ℝ ∞ (imaginaryMomentumLevel lam edge) 0 :=
    contDiffAt_imaginaryMomentumLevel lam edge 0 (by rwa [hzero])
  have hH : fderiv ℝ (fderiv ℝ (imaginaryMomentumLevel lam edge)) 0 =
      momentumHessian lam 0 := by
    rw [imaginaryMomentumLevel_second_fderiv lam edge 0 (by rwa [hzero]), hzero]
  obtain ⟨r, hr, hTaylor⟩ := exists_relative_quadratic_comparison
    (imaginaryMomentumLevel lam edge) hF D.level_zero D.derivative_zero
    (by simpa only [hH] using hpos) (by norm_num : (0 : ℝ) < 1 / 100)
  have hsmall : ∀ᶠ ξ : ℝ in 𝓝 0,
      ‖matrixAction P‖ * Real.sqrt (2 * ξ) < min η (min D.radius r) := by
    have hc : ContinuousAt (fun ξ : ℝ => ‖matrixAction P‖ * Real.sqrt (2 * ξ)) 0 := by
      fun_prop
    exact hc.eventually (gt_mem_nhds (by simpa using lt_min hη (lt_min D.radius_pos hr)))
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff_ball.mp hsmall
  let ξ₀ := min δ (D.quadraticConstant * r ^ 2)
  have hξ₀ : 0 < ξ₀ := lt_min hδ (mul_pos D.quadraticConstant_pos (sq_pos_of_pos hr))
  refine ⟨Q, P, M, ξ₀, hM, hξ₀, hPQ, hQP, hsym, hunit,
    fun x => (hdist x).2, hl1, ?_⟩
  intro ξ hξ hξsmall
  have hξδ : ξ < δ := hξsmall.trans_le (min_le_left _ _)
  have hξr : ξ < D.quadraticConstant * r ^ 2 := hξsmall.trans_le (min_le_right _ _)
  have hfit := hδbound ξ (by simpa only [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos hξ] using hξδ)
  constructor
  · intro β hβ
    have hPQβ : matrixAction P (matrixAction Q β) = β := by
      simp only [matrixAction, ← mul_apply_eq_comp, ← map_mul, hPQ, map_one]
      rfl
    have hn : ‖β‖ < min η (min D.radius r) := by
      calc
        ‖β‖ = ‖matrixAction P (matrixAction Q β)‖ := congrArg norm hPQβ.symm
        _ ≤ ‖matrixAction P‖ * ‖matrixAction Q β‖ := (matrixAction P).le_opNorm _
        _ ≤ ‖matrixAction P‖ * Real.sqrt (2 * ξ) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact hβ.trans (by nlinarith [Real.sqrt_nonneg (2 * ξ)])
        _ < _ := hfit
    have hrβ : ‖β‖ ≤ r := hn.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have ht := (hTaylor β hrβ).2
    rw [hH, ← hmetric β] at ht
    exact ⟨hn.trans_le (min_le_left _ _), mem_ball_zero_iff.mpr
      (hn.trans_le ((min_le_right _ _).trans (min_le_left _ _))),
      relative_level_inner_ellipsoid _ (matrixAction Q) ξ hξ β ht hβ⟩
  · intro β hβ
    have hc := D.quadratic_lower hβ.1
    have hn : ‖β‖ ≤ r := by
      have hs : D.quadraticConstant * ‖β‖ ^ 2 < D.quadraticConstant * r ^ 2 :=
        (hc.trans hβ.2).trans_lt hξr
      by_contra hnr
      have hsq : r ^ 2 ≤ ‖β‖ ^ 2 := (sq_le_sq₀ hr.le (norm_nonneg β)).mpr (not_le.mp hnr).le
      have hm := mul_le_mul_of_nonneg_left hsq D.quadraticConstant_pos.le
      linarith
    have ht := (hTaylor β hn).1
    rw [hH, ← hmetric β] at ht
    exact relative_level_outer_ellipsoid _ (matrixAction Q) ξ hξ β ht hβ.2

end SpectralLevelBodyData

/-- The real pairing in the physical support exponent is controlled by
exactly the same inverse-Hessian metric as the full-block bound. -/
theorem pairing_le_dual_metric (P Q : MomentumSpace →L[ℝ] MomentumSpace)
    (hPQ : ∀ x, P (Q x) = x)
    (hsym : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y)) (v β : MomentumSpace) :
    inner ℝ v β ≤ ‖P v‖ * ‖Q β‖ := by
  have he : inner ℝ v β = inner ℝ (P v) (Q β) := by rw [hsym, hPQ]
  rw [he]
  exact real_inner_le_norm _ _

@[simp] theorem integerMomentum_single (j : Fin 3) :
    integerMomentum (Pi.single j (1 : ℤ)) = PiLp.single 2 j (1 : ℝ) := by
  ext i
  simp [integerMomentum, Pi.single_apply, PiLp.single_apply]

theorem roundedPlacement_column_metric_upper (M : ℕ) (P Q : Mat3)
    (hdist : ∀ x : Vec3, ‖matrixAction (P * roundedPlacementReal M Q) x‖ ≤
      (M : ℝ) * (1 + (1 : ℝ) / 100) * ‖x‖) (j : Fin 3) :
    ‖matrixAction P (integerMomentum (fun i => roundedPlacement M Q i j))‖ ≤
      (M : ℝ) * (1 + (1 : ℝ) / 100) := by
  have he : (fun i => roundedPlacement M Q i j) =
      roundedPlacement M Q *ᵥ Pi.single j 1 := by
    exact (Matrix.mulVec_single_one (roundedPlacement M Q) j).symm
  rw [he, roundedPlacement_integerMomentum]
  have hh := hdist (integerMomentum (Pi.single j (1 : ℤ)))
  simpa only [integerMomentum_single, PiLp.norm_single, norm_one, mul_one,
    matrixAction, map_mul, mul_apply_eq_comp] using hh

/-- Each actual axial support exponent is bounded by the common upper
rate; the same rounded placement supplies the global lower metric rate. -/
theorem roundedPlacement_axial_support_bound (M : ℕ) (P Q : Mat3)
    (hPQ : P * Q = 1)
    (hsym : ∀ x y : Vec3, inner ℝ (matrixAction P x) y = inner ℝ x (matrixAction P y))
    (hdist : ∀ x : Vec3, ‖matrixAction (P * roundedPlacementReal M Q) x‖ ≤
      (M : ℝ) * (1 + (1 : ℝ) / 100) * ‖x‖)
    (ξ : ℝ) (β : MomentumSpace)
    (hβ : ‖matrixAction Q β‖ ≤ (1 + (1 : ℝ) / 100) * Real.sqrt (2 * ξ))
    (j : Fin 3) :
    inner ℝ (integerMomentum (fun i => roundedPlacement M Q i j)) β ≤
      (1 + (1 : ℝ) / 100) ^ 2 * ((M : ℝ) * Real.sqrt (2 * ξ)) := by
  have hPQ' : ∀ x, matrixAction P (matrixAction Q x) = x := by
    intro x
    simp only [matrixAction, ← mul_apply_eq_comp, ← map_mul, hPQ, map_one]
    rfl
  calc
    _ ≤ ‖matrixAction P (integerMomentum (fun i => roundedPlacement M Q i j))‖ *
        ‖matrixAction Q β‖ := pairing_le_dual_metric _ _ hPQ' hsym _ _
    _ ≤ ((M : ℝ) * (1 + (1 : ℝ) / 100)) *
        ((1 + (1 : ℝ) / 100) * Real.sqrt (2 * ξ)) :=
      mul_le_mul (roundedPlacement_column_metric_upper M P Q hdist j) hβ
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem roundedPlacement_rate_margin (M : ℕ) (hM : 0 < M) {ξ : ℝ} (hξ : 0 < ξ) :
    0 < (1 + (1 : ℝ) / 100) ^ 2 * ((M : ℝ) * Real.sqrt (2 * ξ)) ∧
      (1 + (1 : ℝ) / 100) ^ 2 * ((M : ℝ) * Real.sqrt (2 * ξ)) <
        2 * (((1 - (1 : ℝ) / 100) * Real.sqrt (2 * ξ)) *
          ((M : ℝ) * (1 - (1 : ℝ) / 100) / Real.sqrt 3)) := by
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  have hs : 0 < (M : ℝ) * Real.sqrt (2 * ξ) := by positivity
  refine ⟨by positivity, ?_⟩
  convert scaled_placement_rate_margin ((M : ℝ) * Real.sqrt (2 * ξ)) hs using 1
  ring

end Maxwell.Green
