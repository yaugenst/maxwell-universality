import Maxwell.Green.SmoothLocalization
import Maxwell.Green.LocalAssembly
import Maxwell.Green.ChartVolume

/-! Full-torus scalar Green asymptotics from local analytic and geometric data. -/

noncomputable section

open MeasureTheory Set Filter WithLp
open scoped Topology ContDiff InnerProductSpace

namespace Maxwell.Green

def integerMomentum (v : Fin 3 → ℤ) : MomentumSpace := toLp 2 (fun i => (v i : ℝ))

theorem integerMomentum_ne_zero {v : Fin 3 → ℤ} (hv : v ≠ 0) : integerMomentum v ≠ 0 := by
  intro h
  apply hv
  ext i
  have hi := congrArg (fun q : MomentumSpace => q i) h
  change (v i : ℝ) = 0 at hi
  exact_mod_cast hi

theorem integerMomentum_inner (v : Fin 3 → ℤ) (q : MomentumSpace) :
    inner ℝ (integerMomentum v) q = integerPairingCLM v q.ofLp := by
  simp [PiLp.inner_apply, integerMomentum, integerPairingCLM_apply, RCLike.inner_apply, mul_comm]

theorem torusFourierFactor_principalChart
    (v : Fin 3 → ℤ) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace (integerMomentum v)))
    (d : ℕ) (w : ℂ) (u : ℝ) :
    torusFourierFactor d v (ofLp (realPrincipalChart (integerMomentum v) b (w, u))) =
      Complex.exp (Complex.I * ((‖integerMomentum v‖ * (d : ℝ) : ℝ) : ℂ) * u) := by
  unfold torusFourierFactor oscillatoryFactor
  rw [← integerMomentum_inner, realPrincipalChart_phase _ (integerMomentum_ne_zero hv)]
  congr 1
  push_cast
  ring

/-- Local analytic and geometric data for the actual full-torus amplitude.
The structure contains pointwise quotient identities and ordinary smoothness,
root, and Taylor data, with no integral identity or asymptotic premise. -/
structure TorusLocalAssemblyData (v : Fin 3 → ℤ) where
  direction_ne_zero : v ≠ 0
  H : RealTorusCoordinates → ℂ
  L : RealTorusCoordinates → ℂ
  B : RealTorusCoordinates → ℂ
  smooth_H : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 → ContDiffAt ℝ ∞ H q
  smooth_L : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 → ContDiffAt ℝ ∞ L q
  smooth_B : ContDiffAt ℝ ∞ B 0
  residual : (fun q => H q - L q) =ᶠ[𝓝[≠] (0 : RealTorusCoordinates)] B
  support_L : tsupport L ⊆ interior (torusCube (-Real.pi) (2 * Real.pi))
  integrable_L : Integrable L (torusCubeMeasure (-Real.pi) (2 * Real.pi))
  periodic_H : ∀ (i : Fin 3) (q : RealTorusCoordinates),
    H (q + (2 * Real.pi) • Pi.single i 1) = H q
  basis : OrthonormalBasis (Fin 2) ℝ (transverseSpace (integerMomentum v))
  saddle : LocalSaddleData
  regular : RegularNormalData
  numerator : ℂ → ℂ → ℂ
  denominator : ℂ → ℂ → ℂ
  radius : ℝ
  diskRadius : ℝ
  radius_pos : 0 < radius
  radius_disk : 4 * radius ≤ diskRadius
  cutoff_compact : HasCompactSupport saddle.cutoff
  phase_small : ∀ w, saddle.cutoff w ≠ 0 → ‖saddle.phase w‖ ≤ radius / 2
  numerator_analytic : ∀ w, saddle.cutoff w ≠ 0 →
    AnalyticOnNhd ℂ (numerator w) (Metric.closedBall 0 diskRadius)
  denominator_analytic : ∀ w, saddle.cutoff w ≠ 0 →
    AnalyticOnNhd ℂ (denominator w) (Metric.closedBall 0 diskRadius)
  phase_root : ∀ w, saddle.cutoff w ≠ 0 → denominator w (saddle.phase w) = 0
  simple_root : ∀ w, saddle.cutoff w ≠ 0 → deriv (denominator w) (saddle.phase w) ≠ 0
  unique_root : ∀ w, saddle.cutoff w ≠ 0 → ∀ z ∈ Metric.closedBall 0 diskRadius,
    denominator w z = 0 → z = saddle.phase w
  residue_amplitude : ∀ w, saddle.cutoff w ≠ 0 → saddle.amplitude w =
    numerator w (saddle.phase w) / deriv (denominator w) (saddle.phase w)
  regular_amplitude : ∀ w u, regular.amplitude w u =
    (saddle.cutoff w : ℂ) * (scaledPoleCutoff radius u : ℂ) *
      normalCauchyRemainder (numerator w) (denominator w) 0 diskRadius (u : ℂ)
  chart_quotient : ∀ w u,
    L (ofLp (realPrincipalChart (integerMomentum v) basis (w, u))) =
      (saddle.cutoff w : ℂ) * (scaledPoleCutoff radius u : ℂ) *
        (numerator w u / denominator w u)
  normalSpeed : ℝ
  q₁ : ℝ
  q₂ : ℝ
  normalSpeed_pos : 0 < normalSpeed
  q₁_pos : 0 < q₁
  q₂_pos : 0 < q₂
  quadratic_model : saddle.model = quadraticPhase normalSpeed q₁ q₂

namespace TorusLocalAssemblyData

variable {v : Fin 3 → ℤ} (D : TorusLocalAssemblyData v)

def smoothRemainder : RealTorusCoordinates → ℂ := localizedRemainder D.H D.L D.B

theorem smoothRemainder_smooth : SmoothOnTorusCube D.smoothRemainder :=
  localizedRemainder_smoothOnTorusCube D.H D.L D.B D.smooth_H D.smooth_L D.smooth_B D.residual

theorem smoothRemainder_fourier_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, 0 < d →
      ‖∫ q, torusFourierFactor d v q * D.smoothRemainder q
        ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)‖ ≤ C / (d : ℝ) ^ 2 :=
  localizedRemainder_fourier_bound D.H D.L D.B D.smooth_H D.smooth_L D.smooth_B
    D.residual D.support_L D.periodic_H v D.direction_ne_zero

theorem support_localized_subset_cube :
    Function.support D.L ⊆ Set.univ.pi (fun _ : Fin 3 => Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)) := by
  intro q hq i _
  have h := D.support_L (subset_tsupport D.L hq)
  rw [interior_torusCube] at h
  exact ⟨(h i).1, (h i).2.le⟩

theorem integrable_localized_volume : Integrable D.L := by
  have h := D.integrable_L
  rw [torusCubeMeasure_eq_restrict] at h
  exact (integrableOn_iff_integrable_of_support_subset D.support_localized_subset_cube).mp h

/-- The physical Fourier phase and volume-preserving principal chart turn
the actual localized torus integral into the actual local normal quotient. -/
theorem localized_torus_integral_eq_quotient (d : ℕ) :
    (∫ q, torusFourierFactor d v q * D.L q ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)) =
      localizedQuotientIntegral D.saddle D.numerator D.denominator D.radius
        (‖integerMomentum v‖ * (d : ℝ)) := by
  let f := fun q => torusFourierFactor d v q * D.L q
  have hs : Function.support f ⊆ Set.univ.pi
      (fun _ : Fin 3 => Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)) := by
    intro q hq
    apply D.support_localized_subset_cube
    intro hzero
    exact hq (by simp only [f, hzero, mul_zero])
  have hi : Integrable f := D.integrable_localized_volume.bdd_mul
    (continuous_torusFourierFactor d v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => (torusFourierFactor_norm d v q).le)
  have hic := (coordinatePrincipalEquiv_measurePreserving (integerMomentum v)
    (integerMomentum_ne_zero D.direction_ne_zero) D.basis).integrable_comp_of_integrable hi
  have hic' : Integrable (fun z : ℂ × ℝ => f (ofLp (realPrincipalChart (integerMomentum v) D.basis z))) := by
    simpa only [Function.comp_def, coordinatePrincipalEquiv_apply] using hic
  rw [integral_torus_localization_chart (-Real.pi) (2 * Real.pi) f hs
    (integerMomentum v) (integerMomentum_ne_zero D.direction_ne_zero) D.basis hic']
  unfold localizedQuotientIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      dsimp only [f]
      rw [torusFourierFactor_principalChart v D.direction_ne_zero, D.chart_quotient]
      ring

/-- Cauchy's pole formula identifies the localized torus term exactly. -/
theorem localized_torus_integral_eq_localGreen {d : ℕ} (hd : 0 < d) :
    (∫ q, torusFourierFactor d v q * D.L q ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)) =
      localGreenIntegral D.saddle D.regular D.radius (‖integerMomentum v‖ * (d : ℝ)) := by
  rw [D.localized_torus_integral_eq_quotient]
  exact localizedQuotientIntegral_eq D.saddle D.regular D.numerator D.denominator
    D.radius_pos D.radius_disk D.cutoff_compact D.phase_small D.numerator_analytic
    D.denominator_analytic D.phase_root D.simple_root D.unique_root D.residue_amplitude
    D.regular_amplitude (mul_pos (norm_pos_iff.mpr (integerMomentum_ne_zero D.direction_ne_zero))
      (by exact_mod_cast hd))

def normalizedTorusGreen (d : ℕ) : ℂ :=
  ((2 * Real.pi : ℂ) ^ 3)⁻¹ *
    ∫ q, torusFourierFactor d v q * D.H q ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)

def fullScalarGreen (θ σ : ℝ) (d : ℕ) : ℂ :=
  scalarShiftFactor θ σ d * D.normalizedTorusGreen d

def leadingCoefficient : ℂ :=
  scalarLeadingCoefficient D.saddle D.normalSpeed D.q₁ D.q₂ ‖integerMomentum v‖

/-- Exact full-torus decomposition into the normalized local pole calculation
and the actual smooth remainder integral. -/
theorem normalizedTorusGreen_decomposition {d : ℕ} (hd : 0 < d) :
    D.normalizedTorusGreen d =
      normalizedLocalGreen D.saddle D.regular D.radius ‖integerMomentum v‖ d +
      ((2 * Real.pi : ℂ) ^ 3)⁻¹ *
        ∫ q, torusFourierFactor d v q * D.smoothRemainder q
          ∂torusCubeMeasure (-Real.pi) (2 * Real.pi) := by
  unfold normalizedTorusGreen
  rw [localizedRemainder_fourier_decomposition D.H D.L D.B D.integrable_L D.smoothRemainder_smooth,
    D.localized_torus_integral_eq_localGreen hd]
  unfold normalizedLocalGreen smoothRemainder
  ring

/-- The actual normalized full torus coefficient has a non-assumed
`d⁻¹` leading term and an `O(d⁻³ᐟ²)` remainder. -/
theorem normalizedTorusGreen_asymptotic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ d : ℕ in atTop,
      ‖D.normalizedTorusGreen d - D.leadingCoefficient / (d : ℂ)‖ ≤
        C * (d : ℝ) ^ (-(3 : ℝ) / 2) := by
  have hν : 0 < ‖integerMomentum v‖ := norm_pos_iff.mpr (integerMomentum_ne_zero D.direction_ne_zero)
  obtain ⟨C₁, hC₁, hb₁⟩ := normalizedLocalGreen_asymptotic D.saddle D.regular D.radius_pos hν
    D.cutoff_compact D.phase_small D.normalSpeed_pos D.q₁_pos D.q₂_pos D.quadratic_model
  obtain ⟨C₂, hC₂, hb₂⟩ := D.smoothRemainder_fourier_bound
  let N : ℂ := ((2 * Real.pi : ℂ) ^ 3)⁻¹
  refine ⟨C₁ + ‖N‖ * C₂, by positivity, ?_⟩
  have hbn := (show Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop from
    tendsto_natCast_atTop_atTop).eventually hb₁
  filter_upwards [hbn, eventually_ge_atTop (1 : ℕ)] with d hlocal hd
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdrealpos : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hscale : C₂ / (d : ℝ) ^ 2 ≤ C₂ * (d : ℝ) ^ (-(3 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le hdreal (by norm_num : -(2 : ℝ) ≤ -(3 : ℝ) / 2)
    rw [Real.rpow_neg hdrealpos.le, Real.rpow_two] at h
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h hC₂
  have hrem : ‖N * ∫ q, torusFourierFactor d v q * D.smoothRemainder q
      ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)‖ ≤
      (‖N‖ * C₂) * (d : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left ((hb₂ d hdpos).trans hscale) (norm_nonneg N)).trans_eq
      (by ring)
  rw [D.normalizedTorusGreen_decomposition hdpos, add_sub_right_comm]
  exact (norm_add_le _ _).trans ((add_le_add hlocal hrem).trans_eq (by ring))

/-- Reintroducing the contour phase and exponential gives the scalar
asymptotic of the actual full torus Green coefficient. -/
theorem fullScalarGreen_asymptotic (θ σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ d : ℕ in atTop,
      ‖D.fullScalarGreen θ σ d - scalarShiftFactor θ σ d *
        (D.leadingCoefficient / (d : ℂ))‖ ≤
        Real.exp (-σ * (d : ℝ)) * (C * (d : ℝ) ^ (-(3 : ℝ) / 2)) := by
  obtain ⟨C, hC, hb⟩ := D.normalizedTorusGreen_asymptotic
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with d hd
  rw [fullScalarGreen, ← mul_sub, norm_mul, norm_scalarShiftFactor]
  exact mul_le_mul_of_nonneg_left hd (Real.exp_nonneg _)

theorem leadingCoefficient_ne_zero (ha : D.saddle.amplitude0 ≠ 0) : D.leadingCoefficient ≠ 0 :=
  scalarLeadingCoefficient_ne_zero D.saddle D.normalSpeed_pos D.q₁_pos D.q₂_pos
    (norm_pos_iff.mpr (integerMomentum_ne_zero D.direction_ne_zero)) ha

/-- A nonzero residue gives every strict geometric lower rate for the
full torus Green coefficient, after both error terms have been controlled. -/
theorem fullScalarGreen_geometric_lower (ha : D.saddle.amplitude0 ≠ 0)
    (θ σ a : ℝ) (ha₀ : 0 < a) (haσ : a < Real.exp (-σ)) :
    ∀ᶠ d : ℕ in atTop, a ^ d ≤ ‖D.fullScalarGreen θ σ d‖ := by
  let c := ‖D.leadingCoefficient‖
  have hc : 0 < c := norm_pos_iff.mpr (D.leadingCoefficient_ne_zero ha)
  obtain ⟨C, hC, hb⟩ := D.normalizedTorusGreen_asymptotic
  have hsmall := (show Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop from
    tendsto_natCast_atTop_atTop).eventually
      (eventually_polynomial_remainder_small (c / 2) C 1 ((3 : ℝ) / 2)
        (by positivity) (by norm_num))
  have hgeom := eventually_nat_geometric_lower a (c / 2) 1 σ ha₀ (by positivity) haσ
  filter_upwards [hb, hsmall, hgeom, eventually_ge_atTop (1 : ℕ)] with d hd hs hg hdge
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hdge)
  simp only [Real.rpow_one] at hs hg
  have hp : C * (d : ℝ) ^ (-(3 : ℝ) / 2) = |C| / (d : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
      Real.rpow_neg hdpos.le, abs_of_nonneg hC]
    exact (div_eq_mul_inv C _).symm
  rw [hp] at hd
  have herr := hd.trans hs
  have hlead : ‖D.leadingCoefficient / (d : ℂ)‖ = c / (d : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
  have hnorm := norm_le_norm_sub_add (D.leadingCoefficient / (d : ℂ)) (D.normalizedTorusGreen d)
  rw [hlead, norm_sub_rev] at hnorm
  have hlower : (c / 2) / (d : ℝ) ≤ ‖D.normalizedTorusGreen d‖ := by
    have heq : c / (d : ℝ) = 2 * ((c / 2) / (d : ℝ)) := by ring
    linarith
  rw [fullScalarGreen, norm_mul, norm_scalarShiftFactor]
  exact hg.trans (by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hlower (Real.exp_nonneg _))

end TorusLocalAssemblyData
end Maxwell.Green
