import Maxwell.Green.TorusContour
import Maxwell.Green.QuadraticControl
import Maxwell.Green.Singularity
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-! Local positivity of the real part of an analytic edge denominator. -/

noncomputable section

open Set Filter
open scoped Topology ComplexConjugate

namespace Maxwell.Green

/-- An even differentiable real function is stationary at the origin. -/
theorem even_hasDerivAt_zero {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivAt f d 0) (heven : ∀ᶠ t in 𝓝 (0 : ℝ), f (-t) = f t) : d = 0 := by
  have hf' : HasDerivAt f d (-0) := by simpa using hf
  have hneg : HasDerivAt (fun t : ℝ => f (-t)) (-d) 0 := by
    simpa only [Function.comp_def, id_eq, mul_neg, mul_one] using hf'.comp 0 ((hasDerivAt_id (0 : ℝ)).fun_neg)
  have heq : -d = d := (hneg.congr_of_eventuallyEq (heven.mono fun _ h => h.symm)).unique hf
  linarith

/-- The coordinate inclusion is real linear and preserves the supremum norm. -/
def complexifyCLM : RealTorusCoordinates →L[ℝ] ComplexTorusCoordinates :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

@[simp] theorem complexifyCLM_apply (q : RealTorusCoordinates) :
    complexifyCLM q = complexifyCoordinates q := rfl

@[simp] theorem norm_complexifyCoordinates (q : RealTorusCoordinates) :
    ‖complexifyCoordinates q‖ = ‖q‖ := by
  simp only [Pi.norm_def, complexifyCoordinates, Complex.nnnorm_real]

def complexHessian (lam : ComplexTorusCoordinates → ℂ) (z : ComplexTorusCoordinates) :
    ComplexTorusCoordinates →L[ℂ] ComplexTorusCoordinates →L[ℂ] ℂ :=
  fderiv ℂ (fderiv ℂ lam) z

def realDirectionForm
    (B : ComplexTorusCoordinates →L[ℂ] ComplexTorusCoordinates →L[ℂ] ℂ) :
    RealTorusCoordinates →L[ℝ] RealTorusCoordinates →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ RealTorusCoordinates ℂ ℝ Complex.reCLM).comp
    ((B.bilinearRestrictScalars ℝ).bilinearComp complexifyCLM complexifyCLM)

@[simp] theorem realDirectionForm_apply
    (B : ComplexTorusCoordinates →L[ℂ] ComplexTorusCoordinates →L[ℂ] ℂ)
    (q v : RealTorusCoordinates) :
    realDirectionForm B q v = (B (complexifyCoordinates q) (complexifyCoordinates v)).re := rfl

/-- Operator-norm perturbation of the complex Hessian controls its real
quadratic form on every real direction. -/
theorem realDirectionForm_perturbation
    (Q B : ComplexTorusCoordinates →L[ℂ] ComplexTorusCoordinates →L[ℂ] ℂ)
    (a δ : ℝ) (hQ : ∀ q, a * ‖q‖ ^ 2 ≤ realDirectionForm Q q q)
    (hB : ‖B - Q‖ ≤ δ) (q : RealTorusCoordinates) :
    (a - δ) * ‖q‖ ^ 2 ≤ realDirectionForm B q q := by
  let v := complexifyCoordinates q
  have hn : ‖v‖ = ‖q‖ := norm_complexifyCoordinates q
  have hbound : ‖(B - Q) v v‖ ≤ δ * ‖q‖ ^ 2 := calc
    ‖(B - Q) v v‖ ≤ ‖(B - Q) v‖ * ‖v‖ := ((B - Q) v).le_opNorm v
    _ ≤ (‖B - Q‖ * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right ((B - Q).le_opNorm v) (norm_nonneg _)
    _ ≤ (δ * ‖v‖) * ‖v‖ := by gcongr
    _ = δ * ‖q‖ ^ 2 := by rw [hn]; ring
  have hreal := (Complex.abs_re_le_norm ((B - Q) v v)).trans hbound
  change |(B v v).re - (Q v v).re| ≤ δ * ‖q‖ ^ 2 at hreal
  have hl := (abs_le.mp hreal).1
  have hQq := hQ q
  change a * ‖q‖ ^ 2 ≤ (Q v v).re at hQq
  change (a - δ) * ‖q‖ ^ 2 ≤ (B v v).re
  nlinarith

/-- Analyticity and positive real Hessian at zero give uniform positive real
Hessian throughout a complex neighborhood. -/
theorem analytic_exists_positive_complex_hessian_ball
    (lam : ComplexTorusCoordinates → ℂ) (hlam : AnalyticAt ℂ lam 0)
    (hpos : ∀ q : RealTorusCoordinates, q ≠ 0 →
      0 < realDirectionForm (complexHessian lam 0) q q) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧
      (∀ z ∈ Metric.ball (0 : ComplexTorusCoordinates) r, AnalyticAt ℂ lam z) ∧
      ∀ z ∈ Metric.ball (0 : ComplexTorusCoordinates) r, ∀ q : RealTorusCoordinates,
        2 * c * ‖q‖ ^ 2 ≤ realDirectionForm (complexHessian lam z) q q := by
  obtain ⟨a, ha, hmin⟩ := positive_bilinear_has_uniform_lower
    (realDirectionForm (complexHessian lam 0)) hpos
  have hc : 0 < a / 4 := by positivity
  have hH : ContinuousAt (complexHessian lam) 0 := hlam.fderiv.fderiv.continuousAt
  have hnear : ∀ᶠ z in 𝓝 (0 : ComplexTorusCoordinates),
      AnalyticAt ℂ lam z ∧ ‖complexHessian lam z - complexHessian lam 0‖ < a / 2 := by
    have he := hH.eventually (Metric.ball_mem_nhds (complexHessian lam 0)
      (by positivity : (0 : ℝ) < a / 2))
    filter_upwards [hlam.eventually_analyticAt, he] with z hz hz'
    refine ⟨hz, ?_⟩
    change dist (complexHessian lam z) (complexHessian lam 0) < a / 2 at hz'
    have hd : dist (complexHessian lam z) (complexHessian lam 0) =
        ‖complexHessian lam z - complexHessian lam 0‖ := dist_eq_norm (complexHessian lam z) (complexHessian lam 0)
    exact hd ▸ hz'
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  refine ⟨r, a / 4, hr, hc, fun z hz => (hball z hz).1, ?_⟩
  intro z hz q
  have h := realDirectionForm_perturbation (complexHessian lam 0) (complexHessian lam z)
    a (a / 2) hmin (hball z hz).2.le q
  convert h using 1
  ring

def reflectedComplexCoordinates (z : ComplexTorusCoordinates) : ComplexTorusCoordinates :=
  fun i => -conj (z i)

def complexRealLine (q β : RealTorusCoordinates) (t : ℝ) : ComplexTorusCoordinates :=
  t • complexifyCoordinates q + Complex.I • complexifyCoordinates β

@[simp] theorem complexRealLine_zero (q β : RealTorusCoordinates) :
    complexRealLine q β 0 = Complex.I • complexifyCoordinates β := by
  simp [complexRealLine]

@[simp] theorem complexRealLine_one (q β : RealTorusCoordinates) :
    complexRealLine q β 1 = complexifyCoordinates q + Complex.I • complexifyCoordinates β := by
  simp [complexRealLine]

@[simp] theorem reflected_complexRealLine (q β : RealTorusCoordinates) (t : ℝ) :
    reflectedComplexCoordinates (complexRealLine q β t) = complexRealLine q β (-t) := by
  ext i
  simp [reflectedComplexCoordinates, complexRealLine, complexifyCoordinates, Complex.real_smul, add_comm]

theorem hasDerivAt_complexRealLine (q β : RealTorusCoordinates) (t : ℝ) :
    HasDerivAt (complexRealLine q β) (complexifyCoordinates q) t := by
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [complexRealLine, Pi.add_apply, Pi.smul_apply, one_smul, id_eq,
    complexifyCoordinates, smul_eq_mul] using
    ((hasDerivAt_id t).smul_const (q i : ℂ)).add_const (Complex.I * (β i : ℂ))

theorem continuous_complexRealLine (q β : RealTorusCoordinates) :
    Continuous (complexRealLine q β) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_complexRealLine q β t).continuousAt

theorem hasDerivAt_realPart_line
    (lam : ComplexTorusCoordinates → ℂ) (q β : RealTorusCoordinates) (t : ℝ)
    (hlam : AnalyticAt ℂ lam (complexRealLine q β t)) :
    HasDerivAt (fun u => (lam (complexRealLine q β u)).re)
      ((fderiv ℂ lam (complexRealLine q β t)) (complexifyCoordinates q)).re t := by
  have h := (hlam.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (hasDerivAt_complexRealLine q β t)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h

theorem hasDerivAt_realPart_line_derivative
    (lam : ComplexTorusCoordinates → ℂ) (q β : RealTorusCoordinates) (t : ℝ)
    (hlam : AnalyticAt ℂ lam (complexRealLine q β t)) :
    HasDerivAt
      (fun u => ((fderiv ℂ lam (complexRealLine q β u)) (complexifyCoordinates q)).re)
      (realDirectionForm (complexHessian lam (complexRealLine q β t)) q q) t := by
  have h := (hlam.fderiv.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (hasDerivAt_complexRealLine q β t)
  have he : HasDerivAt
      (fun u => (fderiv ℂ lam (complexRealLine q β u)) (complexifyCoordinates q))
      ((complexHessian lam (complexRealLine q β t))
        (complexifyCoordinates q) (complexifyCoordinates q)) t :=
    ((ContinuousLinearMap.apply ℂ ℂ (complexifyCoordinates q)).restrictScalars ℝ).hasFDerivAt
      |>.comp_hasDerivAt t h
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t he

@[simp] theorem norm_imaginary_coordinates (β : RealTorusCoordinates) :
    ‖Complex.I • complexifyCoordinates β‖ = ‖β‖ := by
  rw [norm_smul, Complex.norm_I, one_mul, norm_complexifyCoordinates]

/-- The conjugation symmetry makes the real part even along every real line
through each nearby imaginary point, hence its real directional derivative
vanishes there. -/
theorem realPart_derivative_zero_at_imaginary_point
    (lam : ComplexTorusCoordinates → ℂ) (q β : RealTorusCoordinates)
    {r : ℝ} (hβ : ‖β‖ < r)
    (hlam : AnalyticAt ℂ lam (Complex.I • complexifyCoordinates β))
    (hsym : ∀ z ∈ Metric.ball (0 : ComplexTorusCoordinates) r,
      lam (reflectedComplexCoordinates z) = conj (lam z)) :
    ((fderiv ℂ lam (Complex.I • complexifyCoordinates β)) (complexifyCoordinates q)).re = 0 := by
  have hline : ∀ᶠ t in 𝓝 (0 : ℝ), complexRealLine q β t ∈
      Metric.ball (0 : ComplexTorusCoordinates) r := by
    apply (continuous_complexRealLine q β).continuousAt.eventually
    apply Metric.isOpen_ball.mem_nhds
    simpa only [complexRealLine_zero, mem_ball_zero_iff, norm_imaginary_coordinates] using hβ
  have heven : ∀ᶠ t in 𝓝 (0 : ℝ),
      (lam (complexRealLine q β (-t))).re = (lam (complexRealLine q β t)).re := by
    filter_upwards [hline] with t ht
    have h := congrArg Complex.re (hsym _ ht)
    simpa only [reflected_complexRealLine, Complex.conj_re] using h
  have h := even_hasDerivAt_zero
    (hasDerivAt_realPart_line lam q β 0 (by simpa only [complexRealLine_zero] using hlam)) heven
  simpa only [complexRealLine_zero] using h

/-- Once the Hessian is positive on a complex ball, symmetry gives the
quadratic denominator estimate about every admissible imaginary point. -/
theorem realPart_quadratic_lower_of_complex_hessian
    (lam : ComplexTorusCoordinates → ℂ) (q β : RealTorusCoordinates)
    (r c : ℝ) (hβ : ‖β‖ < r)
    (hline : ∀ t ∈ Icc (0 : ℝ) 1, complexRealLine q β t ∈
      Metric.ball (0 : ComplexTorusCoordinates) r)
    (hlam : ∀ z ∈ Metric.ball (0 : ComplexTorusCoordinates) r, AnalyticAt ℂ lam z)
    (hsym : ∀ z ∈ Metric.ball (0 : ComplexTorusCoordinates) r,
      lam (reflectedComplexCoordinates z) = conj (lam z))
    (hH : ∀ z ∈ Metric.ball (0 : ComplexTorusCoordinates) r,
      ∀ v : RealTorusCoordinates, 2 * c * ‖v‖ ^ 2 ≤ realDirectionForm (complexHessian lam z) v v) :
    (lam (Complex.I • complexifyCoordinates β)).re + c * ‖q‖ ^ 2 ≤
      (lam (complexifyCoordinates q + Complex.I • complexifyCoordinates β)).re := by
  have hβmem : Complex.I • complexifyCoordinates β ∈
      Metric.ball (0 : ComplexTorusCoordinates) r := by
    simpa only [mem_ball_zero_iff, norm_imaginary_coordinates] using hβ
  have hstationary := realPart_derivative_zero_at_imaginary_point lam q β hβ
    (hlam _ hβmem) hsym
  have h := quadratic_taylor_lower_unit
    (fun t => (lam (complexRealLine q β t)).re)
    (fun t => ((fderiv ℂ lam (complexRealLine q β t)) (complexifyCoordinates q)).re)
    (fun t => realDirectionForm (complexHessian lam (complexRealLine q β t)) q q)
    (c * ‖q‖ ^ 2)
    (fun t ht => hasDerivAt_realPart_line lam q β t (hlam _ (hline t ht)))
    (fun t ht => hasDerivAt_realPart_line_derivative lam q β t (hlam _ (hline t ht)))
    (fun t ht => by simpa only [mul_assoc] using hH _ (hline t ht) q)
  simpa only [complexRealLine_zero, complexRealLine_one, hstationary, add_zero] using h

theorem norm_complexRealLine_le (q β : RealTorusCoordinates) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ‖complexRealLine q β t‖ ≤ ‖q‖ + ‖β‖ := by
  calc
    ‖complexRealLine q β t‖ ≤ ‖t • complexifyCoordinates q‖ +
        ‖Complex.I • complexifyCoordinates β‖ := norm_add_le _ _
    _ = t * ‖q‖ + ‖β‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
        norm_complexifyCoordinates, norm_imaginary_coordinates]
    _ ≤ ‖q‖ + ‖β‖ := by nlinarith [norm_nonneg q, ht.2]

/-- Analyticity, the actual positive real Hessian, and conjugation symmetry
imply the local quadratic lower bound for the real part of the denominator.
No derivative or quadratic estimate is assumed in this result. -/
theorem analytic_edge_denominator_quadratic_bound
    (lam : ComplexTorusCoordinates → ℂ) (hlam : AnalyticAt ℂ lam 0)
    (hpos : ∀ q : RealTorusCoordinates, q ≠ 0 →
      0 < realDirectionForm (complexHessian lam 0) q q)
    (hsym : ∀ᶠ z in 𝓝 (0 : ComplexTorusCoordinates),
      lam (reflectedComplexCoordinates z) = conj (lam z)) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ q β : RealTorusCoordinates, ‖q‖ < δ → ‖β‖ < δ → ∀ E : ℝ,
        (lam (Complex.I • complexifyCoordinates β)).re - E + c * ‖q‖ ^ 2 ≤
          (lam (complexifyCoordinates q + Complex.I • complexifyCoordinates β) - (E : ℂ)).re := by
  obtain ⟨rH, c, hrH, hc, hanalytic, hH⟩ :=
    analytic_exists_positive_complex_hessian_ball lam hlam hpos
  obtain ⟨rS, hrS, hS⟩ := Metric.eventually_nhds_iff_ball.mp hsym
  let r := min rH rS
  have hr : 0 < r := lt_min hrH hrS
  have hrH' : r ≤ rH := min_le_left _ _
  have hrS' : r ≤ rS := min_le_right _ _
  refine ⟨r / 3, c, by positivity, hc, ?_⟩
  intro q β hq hβ E
  have hline : ∀ t ∈ Icc (0 : ℝ) 1,
      complexRealLine q β t ∈ Metric.ball (0 : ComplexTorusCoordinates) r := by
    intro t ht
    apply mem_ball_zero_iff.mpr
    have hn := norm_complexRealLine_le q β ht
    linarith
  have h := realPart_quadratic_lower_of_complex_hessian lam q β r c
    (by linarith : ‖β‖ < r) hline
    (fun z hz => hanalytic z (Metric.ball_subset_ball hrH' hz))
    (fun z hz => hS z (Metric.ball_subset_ball hrS' hz))
    (fun z hz => hH z (Metric.ball_subset_ball hrH' hz))
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

/-- Positive quadratic control excludes real-energy poles off the origin. -/
theorem denominator_ne_zero_of_quadratic_bound
    (lam : ComplexTorusCoordinates → ℂ) (q β : RealTorusCoordinates)
    (E c : ℝ) (hc : 0 < c) (hq : q ≠ 0)
    (hgap : E ≤ (lam (Complex.I • complexifyCoordinates β)).re)
    (hbound : (lam (Complex.I • complexifyCoordinates β)).re - E + c * ‖q‖ ^ 2 ≤
      (lam (complexifyCoordinates q + Complex.I • complexifyCoordinates β) - (E : ℂ)).re) :
    lam (complexifyCoordinates q + Complex.I • complexifyCoordinates β) - (E : ℂ) ≠ 0 := by
  have hqpos : 0 < c * ‖q‖ ^ 2 := mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hq))
  intro heq
  rw [heq, Complex.zero_re] at hbound
  linarith

/-- A strict imaginary-point gap also excludes the origin, hence yields
invertibility throughout the whole small real contour. -/
theorem denominator_ne_zero_of_strict_gap
    (lam : ComplexTorusCoordinates → ℂ) (q β : RealTorusCoordinates)
    (E c : ℝ) (hc : 0 ≤ c)
    (hgap : E < (lam (Complex.I • complexifyCoordinates β)).re)
    (hbound : (lam (Complex.I • complexifyCoordinates β)).re - E + c * ‖q‖ ^ 2 ≤
      (lam (complexifyCoordinates q + Complex.I • complexifyCoordinates β) - (E : ℂ)).re) :
    lam (complexifyCoordinates q + Complex.I • complexifyCoordinates β) - (E : ℂ) ≠ 0 := by
  intro heq
  rw [heq, Complex.zero_re] at hbound
  nlinarith [mul_nonneg hc (sq_nonneg ‖q‖)]

/-- The supremum norm of the three coordinates is bounded by their
Euclidean norm. -/
theorem norm_coordinates_le_euclidean (q : Momentum) : ‖q.ofLp‖ ≤ ‖q‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).mpr
  exact fun i => PiLp.norm_apply_le q i

/-- In dimension three the Euclidean square is at most three times the
coordinate supremum square. -/
theorem euclidean_norm_sq_le_three_coordinates (q : Momentum) :
    ‖q‖ ^ 2 ≤ 3 * ‖q.ofLp‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    ∑ i : Fin 3, ‖q.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, ‖q.ofLp‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm q.ofLp i) 2
    _ = 3 * ‖q.ofLp‖ ^ 2 := by simp

/-- The analytic edge assumptions give the actual integrable inverse-square
majorant uniformly over all nearby imaginary points with nonnegative gap. -/
theorem analytic_edge_inverseSquare_bound
    (lam : ComplexTorusCoordinates → ℂ) (hlam : AnalyticAt ℂ lam 0)
    (hpos : ∀ q : RealTorusCoordinates, q ≠ 0 →
      0 < realDirectionForm (complexHessian lam 0) q q)
    (hsym : ∀ᶠ z in 𝓝 (0 : ComplexTorusCoordinates),
      lam (reflectedComplexCoordinates z) = conj (lam z)) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (q : Momentum) (β : RealTorusCoordinates), ‖q‖ < δ → ‖β‖ < δ → q ≠ 0 →
      ∀ E : ℝ, E ≤ (lam (Complex.I • complexifyCoordinates β)).re →
        ‖(lam (complexifyCoordinates q.ofLp + Complex.I • complexifyCoordinates β) - (E : ℂ))⁻¹‖ ≤
          C * inverseSquare q := by
  obtain ⟨δ, c, hδ, hc, hbound⟩ := analytic_edge_denominator_quadratic_bound lam hlam hpos hsym
  refine ⟨δ, (c / 3)⁻¹, hδ, by positivity, ?_⟩
  intro q β hq hβ hqne E hE
  have hq' : ‖q.ofLp‖ < δ := (norm_coordinates_le_euclidean q).trans_lt hq
  have h := hbound q.ofLp β hq' hβ E
  have hs := mul_le_mul_of_nonneg_left (euclidean_norm_sq_le_three_coordinates q)
    (show 0 ≤ c / 3 by positivity)
  apply norm_inv_le_inverseSquare (c / 3) (by positivity) q hqne
  nlinarith

end Maxwell.Green

