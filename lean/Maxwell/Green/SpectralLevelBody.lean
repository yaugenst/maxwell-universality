import Maxwell.Green.ImaginaryJet
import Maxwell.Green.LocalSupport
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Local analytic spectral data construct the actual compact strictly
convex imaginary-momentum level body and its regular support points. -/

noncomputable section

namespace Maxwell.Green

open Set Filter Metric Complex
open scoped Topology InnerProductSpace ContDiff

theorem contDiffAt_imaginaryMomentumLevel
    (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ) (β : MomentumSpace)
    (hlam : AnalyticAt ℂ lam (Complex.I • momentumComplex β)) :
    ContDiffAt ℝ ∞ (imaginaryMomentumLevel lam edge) β := by
  let J : MomentumSpace →L[ℝ] ComplexTorusCoordinates := Complex.I • momentumComplexCLM
  have h : ContDiffAt ℝ ∞ lam (J β) := hlam.restrictScalars.contDiffAt
  exact contDiffAt_const.sub
    (Complex.reCLM.contDiff.contDiffAt.comp β (h.comp β J.contDiff.contDiffAt))

/-- The Hessian of the actual imaginary-momentum level is the real part
of the complex momentum Hessian, with the signs fixed by the two factors of `I`. -/
theorem imaginaryMomentumLevel_second_fderiv
    (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ) (β : MomentumSpace)
    (hlam : AnalyticAt ℂ lam (Complex.I • momentumComplex β)) :
    fderiv ℝ (fderiv ℝ (imaginaryMomentumLevel lam edge)) β =
      momentumHessian lam (Complex.I • momentumComplex β) := by
  let J : MomentumSpace →L[ℝ] ComplexTorusCoordinates := Complex.I • momentumComplexCLM
  have hcd := contDiffAt_imaginaryMomentumLevel lam edge β hlam
  have hd : DifferentiableAt ℝ (fderiv ℝ (imaginaryMomentumLevel lam edge)) β :=
    (hcd.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  ext x y
  have he : (fun z => (fderiv ℝ (imaginaryMomentumLevel lam edge) z) y) =ᶠ[𝓝 β]
      (fun z => ((fderiv ℂ lam (J z)) (momentumComplex y)).im) := by
    filter_upwards [J.continuous.continuousAt.tendsto.eventually hlam.eventually_analyticAt] with z hz
    exact imaginaryMomentumLevel_directional_derivative lam edge z y hz
  have hreal := (ContinuousLinearMap.apply ℝ ℝ y).hasFDerivAt.comp β hd.hasFDerivAt
  have hc := (hlam.fderiv.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp β J.hasFDerivAt
  have hev := ((ContinuousLinearMap.apply ℂ ℂ (momentumComplex y)).restrictScalars ℝ).hasFDerivAt.comp β hc
  have him := Complex.imCLM.hasFDerivAt.comp β hev
  have heq := hreal.unique (him.congr_of_eventuallyEq he)
  have hx := congrArg (fun L : MomentumSpace →L[ℝ] ℝ => L x) heq
  change ((fderiv ℝ (fderiv ℝ (imaginaryMomentumLevel lam edge)) β) x) y =
    (((fderiv ℂ (fderiv ℂ lam) (Complex.I • momentumComplex β))
      (Complex.I • momentumComplex x)) (momentumComplex y)).im at hx
  simpa only [map_smul, smul_apply, smul_eq_mul,
    Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
    momentumHessian_apply, complexHessian] using hx

theorem continuousAt_imaginaryMomentumLevel_hessian
    (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ) (β : MomentumSpace)
    (hlam : AnalyticAt ℂ lam (Complex.I • momentumComplex β)) :
    ContinuousAt (fderiv ℝ (fderiv ℝ (imaginaryMomentumLevel lam edge))) β :=
  ((contDiffAt_imaginaryMomentumLevel lam edge β hlam).fderiv_right
    (m := ∞) (by simp)).continuousAt_fderiv (by simp)

theorem continuousAt_momentumHessian_imaginary
    (lam : ComplexTorusCoordinates → ℂ) (β : MomentumSpace)
    (hlam : AnalyticAt ℂ lam (Complex.I • momentumComplex β)) :
    ContinuousAt (fun b => momentumHessian lam (Complex.I • momentumComplex b)) β := by
  let J : MomentumSpace →L[ℝ] ComplexTorusCoordinates := Complex.I • momentumComplexCLM
  have he : (fun b => momentumHessian lam (Complex.I • momentumComplex b)) =ᶠ[𝓝 β]
      fderiv ℝ (fderiv ℝ (imaginaryMomentumLevel lam 0)) := by
    filter_upwards [J.continuous.continuousAt.tendsto.eventually hlam.eventually_analyticAt] with b hb
    exact (imaginaryMomentumLevel_second_fderiv lam 0 b hb).symm
  exact (continuousAt_imaginaryMomentumLevel_hessian lam 0 β hlam).congr_of_eventuallyEq he

section LocalBody

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- The local sublevel theorem needs continuity only on its chart. -/
theorem local_sublevel_body_of_continuousOn
    (F : E → ℝ) (r c ε : ℝ) (hF : ContinuousOn F (closedBall (0 : E) r))
    (hr : 0 < r) (hc : 0 < c) (hε : F 0 < ε) (hεr : ε < c * r ^ 2)
    (hstrict : StrictConvexOn ℝ (closedBall (0 : E) r) F)
    (hlower : ∀ x ∈ closedBall (0 : E) r, c * ‖x‖ ^ 2 ≤ F x) :
    IsCompact {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε} ∧
      StrictConvex ℝ {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε} ∧
      (0 : E) ∈ interior {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε} := by
  let s := {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε}
  have hinside : s ⊆ ball (0 : E) r :=
    local_sublevel_subset_ball F r c ε hr hc hεr hlower
  have hinterior {x : E} (hx : x ∈ ball (0 : E) r) (he : F x < ε) :
      x ∈ interior s := by
    apply mem_interior_iff_mem_nhds.mpr
    have hcont := hF.continuousAt (closedBall_mem_nhds_of_mem hx)
    filter_upwards [isOpen_ball.mem_nhds hx, hcont.eventually (gt_mem_nhds he)] with y hy hye
    exact ⟨ball_subset_closedBall hy, hye.le⟩
  refine ⟨(isCompact_closedBall (0 : E) r).of_isClosed_subset
    (isClosed_closedBall.isClosed_le hF continuousOn_const) (fun _ hx => hx.1), ?_, ?_⟩
  · intro x hx y hy hxy a b ha hb hab
    apply hinterior (convex_ball (0 : E) r (hinside hx) (hinside hy) ha.le hb.le hab)
    have hlt := hstrict.2 hx.1 hy.1 hxy ha hb hab
    have hupper : a * F x + b * F y ≤ ε := by
      have h₁ := mul_le_mul_of_nonneg_left hx.2 ha.le
      have h₂ := mul_le_mul_of_nonneg_left hy.2 hb.le
      have hsum : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
      linarith
    exact hlt.trans_le hupper
  · exact hinterior (mem_ball_self hr) hε

/-- A positive Hessian at a stationary zero yields quantitative control on
one closed chart. The radius may be restricted to any chosen neighborhood. -/
theorem exists_positive_hessian_local_chart
    (F : E → ℝ) (hF : ContDiffAt ℝ ∞ F 0)
    (hpos : ∀ y, y ≠ 0 → 0 < (fderiv ℝ (fderiv ℝ F) 0) y y)
    (hFzero : F 0 = 0) (hDFzero : fderiv ℝ F 0 = 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ r c : ℝ, 0 < r ∧ r < η ∧ 0 < c ∧
      (∀ x ∈ closedBall (0 : E) r, ContDiffAt ℝ 2 F x) ∧
      (∀ x ∈ closedBall (0 : E) r, ∀ y,
        2 * c * ‖y‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ F) x) y y) ∧
      (∀ x ∈ closedBall (0 : E) r, c * ‖x‖ ^ 2 ≤ F x) ∧
      StrictConvexOn ℝ (closedBall (0 : E) r) F := by
  let DF := fderiv ℝ F
  let H := fderiv ℝ DF
  have hDF : ContDiffAt ℝ 2 DF 0 := hF.fderiv_right (by norm_num)
  have hHcont : Tendsto (fun x => ‖H x - H 0‖) (𝓝 (0 : E)) (𝓝 (0 : ℝ)) := by
    have h : ContinuousAt (fun x => H x - H 0) (0 : E) :=
      (hDF.continuousAt_fderiv (by norm_num)).sub continuousAt_const
    have hn : ContinuousAt (fun x => ‖H x - H 0‖) (0 : E) :=
      @ContinuousAt.norm E (E →L[ℝ] E →L[ℝ] ℝ) _ _ _ _ h
    have hz : ‖(0 : E →L[ℝ] E →L[ℝ] ℝ)‖ = 0 := ContinuousLinearMap.opNorm_zero
    simpa only [sub_self, hz] using hn.tendsto
  obtain ⟨a, ha, hlower⟩ := positive_bilinear_has_uniform_lower (H 0) hpos
  let c : ℝ := a / 4
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨rH, hrH, hnearH⟩ := exists_ball_hessian_lower H hHcont c hc
    (fun y => by dsimp [c]; nlinarith [hlower y])
  have hC2 : ∀ᶠ x in 𝓝 (0 : E), ContDiffAt ℝ 2 F x :=
    (hF.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ ∞)).eventually (by norm_num)
  obtain ⟨rD, hrD, hnearD⟩ := Metric.eventually_nhds_iff_ball.mp hC2
  let r : ℝ := min η (min rH rD) / 2
  have hm : 0 < min η (min rH rD) := lt_min hη (lt_min hrH hrD)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrη : r < η := (half_lt_self hm).trans_le (min_le_left _ _)
  have hrH' : r < rH := (half_lt_self hm).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hrD' : r < rD := (half_lt_self hm).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have hD (x : E) (hx : x ∈ closedBall (0 : E) r) : ContDiffAt ℝ 2 F x :=
    hnearD x (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx).trans_lt hrD'))
  have hH (x : E) (hx : x ∈ closedBall (0 : E) r) (y : E) :
      2 * c * ‖y‖ ^ 2 ≤ H x y y :=
    hnearH x (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx).trans_lt hrH')) y
  have hd (x : E) (hx : x ∈ closedBall (0 : E) r) : HasFDerivAt F (DF x) x :=
    (hD x hx).differentiableAt (by norm_num) |>.hasFDerivAt
  have hdd (x : E) (hx : x ∈ closedBall (0 : E) r) : HasFDerivAt DF (H x) x :=
    ((hD x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  refine ⟨r, c, hr, hrη, hc, hD, hH, ?_, ?_⟩
  · intro x hx
    exact quadratic_coercivity_on (convex_closedBall (0 : E) r) (mem_closedBall_self hr.le)
      F DF H c hd hdd hH hFzero hDFzero hx
  · exact strictConvexOn_of_hessian_lower (convex_closedBall (0 : E) r)
      F DF H c hc hd hdd hH

end LocalBody

def spectralLevelGradient (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ)
    (β : MomentumSpace) : MomentumSpace :=
  (InnerProductSpace.toDual ℝ MomentumSpace).symm
    (fderiv ℝ (imaginaryMomentumLevel lam edge) β)

theorem innerSL_spectralLevelGradient (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ)
    (β : MomentumSpace) :
    innerSL ℝ (spectralLevelGradient lam edge β) =
      fderiv ℝ (imaginaryMomentumLevel lam edge) β := by
  ext x
  exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := MomentumSpace)
    (y := fderiv ℝ (imaginaryMomentumLevel lam edge) β) (x := x)

/-- A chart constructed from the actual analytic spectral function. -/
structure SpectralLevelBodyData (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  quadraticConstant : ℝ
  quadraticConstant_pos : 0 < quadraticConstant
  level_zero : imaginaryMomentumLevel lam edge 0 = 0
  derivative_zero : fderiv ℝ (imaginaryMomentumLevel lam edge) 0 = 0
  local_analytic : ∀ β ∈ closedBall (0 : MomentumSpace) radius,
    AnalyticAt ℂ lam (Complex.I • momentumComplex β)
  hessian_lower : ∀ β ∈ closedBall (0 : MomentumSpace) radius, ∀ x,
    2 * quadraticConstant * ‖x‖ ^ 2 ≤ momentumHessian lam (Complex.I • momentumComplex β) x x

namespace SpectralLevelBodyData

variable {lam : ComplexTorusCoordinates → ℂ} {edge : ℝ} (D : SpectralLevelBodyData lam edge)

def body (ξ : ℝ) : Set MomentumSpace :=
  {β | β ∈ closedBall (0 : MomentumSpace) D.radius ∧ imaginaryMomentumLevel lam edge β ≤ ξ}

theorem hasFDerivAt {β : MomentumSpace} (hβ : β ∈ closedBall (0 : MomentumSpace) D.radius) :
    HasFDerivAt (imaginaryMomentumLevel lam edge)
      (fderiv ℝ (imaginaryMomentumLevel lam edge) β) β :=
  ((contDiffAt_imaginaryMomentumLevel lam edge β (D.local_analytic β hβ)).differentiableAt
    (by simp)).hasFDerivAt

theorem hasFDerivAt_derivative {β : MomentumSpace}
    (hβ : β ∈ closedBall (0 : MomentumSpace) D.radius) :
    HasFDerivAt (fderiv ℝ (imaginaryMomentumLevel lam edge))
      (momentumHessian lam (Complex.I • momentumComplex β)) β := by
  rw [← imaginaryMomentumLevel_second_fderiv lam edge β (D.local_analytic β hβ)]
  exact ((contDiffAt_imaginaryMomentumLevel lam edge β (D.local_analytic β hβ)).fderiv_right
    (m := ∞) (by simp)).differentiableAt (by simp) |>.hasFDerivAt

theorem hasStrictFDerivAt_gradient {β : MomentumSpace}
    (hβ : β ∈ closedBall (0 : MomentumSpace) D.radius) :
    HasStrictFDerivAt (imaginaryMomentumLevel lam edge)
      (innerSL ℝ (spectralLevelGradient lam edge β)) β := by
  rw [innerSL_spectralLevelGradient]
  exact (contDiffAt_imaginaryMomentumLevel lam edge β (D.local_analytic β hβ)).hasStrictFDerivAt
    (by simp)

theorem quadratic_lower {β : MomentumSpace}
    (hβ : β ∈ closedBall (0 : MomentumSpace) D.radius) :
    D.quadraticConstant * ‖β‖ ^ 2 ≤ imaginaryMomentumLevel lam edge β :=
  quadratic_coercivity_on (convex_closedBall (0 : MomentumSpace) D.radius)
    (mem_closedBall_self D.radius_pos.le) (imaginaryMomentumLevel lam edge)
    (fderiv ℝ (imaginaryMomentumLevel lam edge))
    (fun β => momentumHessian lam (Complex.I • momentumComplex β)) D.quadraticConstant
    (fun _ hx => D.hasFDerivAt hx) (fun _ hx => D.hasFDerivAt_derivative hx)
    D.hessian_lower D.level_zero D.derivative_zero hβ

theorem strictConvexOn : StrictConvexOn ℝ (closedBall (0 : MomentumSpace) D.radius)
    (imaginaryMomentumLevel lam edge) :=
  strictConvexOn_of_hessian_lower (convex_closedBall (0 : MomentumSpace) D.radius)
    (imaginaryMomentumLevel lam edge) (fderiv ℝ (imaginaryMomentumLevel lam edge))
    (fun β => momentumHessian lam (Complex.I • momentumComplex β)) D.quadraticConstant
    D.quadraticConstant_pos (fun _ hx => D.hasFDerivAt hx)
    (fun _ hx => D.hasFDerivAt_derivative hx) D.hessian_lower

theorem body_properties {ξ : ℝ} (hξ : 0 < ξ)
    (hξr : ξ < D.quadraticConstant * D.radius ^ 2) :
    IsCompact (D.body ξ) ∧ StrictConvex ℝ (D.body ξ) ∧
      (0 : MomentumSpace) ∈ interior (D.body ξ) ∧
      D.body ξ ⊆ ball (0 : MomentumSpace) D.radius := by
  obtain ⟨hcompact, hstrict, hzero⟩ := local_sublevel_body_of_continuousOn
    (imaginaryMomentumLevel lam edge) D.radius D.quadraticConstant ξ
    (fun _ hx => (D.hasFDerivAt hx).continuousAt.continuousWithinAt)
    D.radius_pos D.quadraticConstant_pos (by simpa only [D.level_zero] using hξ)
    hξr D.strictConvexOn (fun _ hx => D.quadratic_lower hx)
  exact ⟨hcompact, hstrict, hzero, local_sublevel_subset_ball (imaginaryMomentumLevel lam edge)
    D.radius D.quadraticConstant ξ D.radius_pos D.quadraticConstant_pos hξr
    (fun _ hx => D.quadratic_lower hx)⟩

theorem gradient_ne_zero {ξ : ℝ} (hξ : 0 < ξ) {β : MomentumSpace}
    (hβ : β ∈ closedBall (0 : MomentumSpace) D.radius)
    (hlevel : imaginaryMomentumLevel lam edge β = ξ) : spectralLevelGradient lam edge β ≠ 0 := by
  have hd := derivative_ne_zero_of_quadratic_lower (mem_closedBall_self D.radius_pos.le)
    (imaginaryMomentumLevel lam edge) (fderiv ℝ (imaginaryMomentumLevel lam edge))
    D.quadraticConstant D.quadraticConstant_pos.le
    (fun _ hx _ hy => quadratic_taylor_lower_on (convex_closedBall (0 : MomentumSpace) D.radius)
      (imaginaryMomentumLevel lam edge) (fderiv ℝ (imaginaryMomentumLevel lam edge))
      (fun β => momentumHessian lam (Complex.I • momentumComplex β)) D.quadraticConstant
      (fun _ hz => D.hasFDerivAt hz) (fun _ hz => D.hasFDerivAt_derivative hz)
      D.hessian_lower hx hy) hβ (by simpa only [D.level_zero, hlevel] using hξ)
  intro hz
  apply hd
  rw [← innerSL_spectralLevelGradient, hz, map_zero]

/-- Every nonzero direction has exactly one support point on each small
positive spectral level, with an actual positive gradient multiplier. -/
theorem exists_unique_support_point {ξ : ℝ} (hξ : 0 < ξ)
    (hξr : ξ < D.quadraticConstant * D.radius ^ 2) (v : MomentumSpace) (hv : v ≠ 0) :
    ∃! β : MomentumSpace, β ∈ ball (0 : MomentumSpace) D.radius ∧
      imaginaryMomentumLevel lam edge β = ξ ∧
      IsMaxOn (fun x => ⟪v, x⟫_ℝ) (D.body ξ) β ∧
      ∃ χ : ℝ, 0 < χ ∧ spectralLevelGradient lam edge β = χ • v := by
  obtain ⟨hc, hs, hz, hi⟩ := D.body_properties hξ hξr
  exact exists_unique_regular_local_support_point (imaginaryMomentumLevel lam edge)
    (spectralLevelGradient lam edge) D.radius ξ hc hs hz hi
    (fun _ hx => D.hasStrictFDerivAt_gradient (ball_subset_closedBall hx))
    (fun _ hx hl => D.gradient_ne_zero hξ (ball_subset_closedBall hx) hl) v hv

theorem support_pairing_pos {ξ : ℝ} (hξ : 0 < ξ)
    (hξr : ξ < D.quadraticConstant * D.radius ^ 2) {v β : MomentumSpace} (hv : v ≠ 0)
    (hmax : IsMaxOn (fun x => ⟪v, x⟫_ℝ) (D.body ξ) β) : 0 < ⟪v, β⟫_ℝ :=
  Maxwell.Green.support_pairing_pos (D.body_properties hξ hξr).2.2.1 hv hmax

end SpectralLevelBodyData

/-- Local spectral analyticity, stationarity, and the positive real
momentum Hessian construct the support body; no global extension is used. -/
theorem exists_spectralLevelBodyData_within
    (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ)
    (hlam : AnalyticAt ℂ lam 0) (hvalue : lam 0 = (edge : ℂ))
    (hstationary : fderiv ℂ lam 0 = 0)
    (hpositive : ∀ x : MomentumSpace, x ≠ 0 → 0 < momentumHessian lam 0 x x)
    {η : ℝ} (hη : 0 < η) :
    ∃ D : SpectralLevelBodyData lam edge, D.radius < η := by
  let F := imaginaryMomentumLevel lam edge
  let J : MomentumSpace →L[ℝ] ComplexTorusCoordinates := Complex.I • momentumComplexCLM
  have hJ₀ : Complex.I • momentumComplex (0 : MomentumSpace) = 0 := by
    ext j
    simp [momentumComplex]
  have hA₀ : AnalyticAt ℂ lam (Complex.I • momentumComplex (0 : MomentumSpace)) := by
    simpa only [hJ₀] using hlam
  have hF : ContDiffAt ℝ ∞ F 0 := contDiffAt_imaginaryMomentumLevel lam edge 0 hA₀
  have hFzero : F 0 = 0 := by simp only [F, imaginaryMomentumLevel, hJ₀, hvalue, ofReal_re, sub_self]
  have hDFzero : fderiv ℝ F 0 = 0 := by
    ext x
    rw [imaginaryMomentumLevel_directional_derivative lam edge 0 x hA₀, hJ₀, hstationary]
    simp
  have hpos : ∀ x : MomentumSpace, x ≠ 0 → 0 < (fderiv ℝ (fderiv ℝ F) 0) x x := by
    rw [imaginaryMomentumLevel_second_fderiv lam edge 0 hA₀, hJ₀]
    exact hpositive
  have hnear : ∀ᶠ β : MomentumSpace in 𝓝 0, AnalyticAt ℂ lam (Complex.I • momentumComplex β) :=
    J.continuous.continuousAt.tendsto.eventually hA₀.eventually_analyticAt
  obtain ⟨rA, hrA, hnearA⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  obtain ⟨r, c, hr, hrsmall, hc, _, hH, _, _⟩ := exists_positive_hessian_local_chart
    F hF hpos hFzero hDFzero (lt_min hη hrA)
  have hrη : r < η := hrsmall.trans_le (min_le_left _ _)
  have hrA' : r < rA := hrsmall.trans_le (min_le_right _ _)
  have hlocal (β : MomentumSpace) (hβ : β ∈ closedBall (0 : MomentumSpace) r) :
      AnalyticAt ℂ lam (Complex.I • momentumComplex β) :=
    hnearA β (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hβ).trans_lt hrA'))
  refine ⟨{
    radius := r
    radius_pos := hr
    quadraticConstant := c
    quadraticConstant_pos := hc
    level_zero := hFzero
    derivative_zero := hDFzero
    local_analytic := hlocal
    hessian_lower := ?_
  }, hrη⟩
  intro β hβ x
  rw [← imaginaryMomentumLevel_second_fderiv lam edge β (hlocal β hβ)]
  exact hH β hβ x

theorem exists_spectralLevelBodyData
    (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ)
    (hlam : AnalyticAt ℂ lam 0) (hvalue : lam 0 = (edge : ℂ))
    (hstationary : fderiv ℂ lam 0 = 0)
    (hpositive : ∀ x : MomentumSpace, x ≠ 0 → 0 < momentumHessian lam 0 x x) :
    Nonempty (SpectralLevelBodyData lam edge) := by
  obtain ⟨D, _⟩ := exists_spectralLevelBodyData_within lam edge hlam hvalue hstationary
    hpositive zero_lt_one
  exact ⟨D⟩

/-- The support-point family with all geometry constructed from the
stationary analytic band and its positive momentum Hessian. -/
theorem exists_spectral_support_family
    (lam : ComplexTorusCoordinates → ℂ) (edge : ℝ)
    (hlam : AnalyticAt ℂ lam 0) (hvalue : lam 0 = (edge : ℂ))
    (hstationary : fderiv ℂ lam 0 = 0)
    (hpositive : ∀ x : MomentumSpace, x ≠ 0 → 0 < momentumHessian lam 0 x x) :
    ∃ r ξ₀ : ℝ, 0 < r ∧ 0 < ξ₀ ∧ ∀ ξ : ℝ, 0 < ξ → ξ < ξ₀ →
      IsCompact {β | β ∈ closedBall (0 : MomentumSpace) r ∧
        imaginaryMomentumLevel lam edge β ≤ ξ} ∧
      StrictConvex ℝ {β | β ∈ closedBall (0 : MomentumSpace) r ∧
        imaginaryMomentumLevel lam edge β ≤ ξ} ∧
      (0 : MomentumSpace) ∈ interior {β | β ∈ closedBall (0 : MomentumSpace) r ∧
        imaginaryMomentumLevel lam edge β ≤ ξ} ∧
      ∀ v : MomentumSpace, v ≠ 0 → ∃! β : MomentumSpace,
        β ∈ ball (0 : MomentumSpace) r ∧ imaginaryMomentumLevel lam edge β = ξ ∧
        IsMaxOn (fun x => ⟪v, x⟫_ℝ)
          {x | x ∈ closedBall (0 : MomentumSpace) r ∧ imaginaryMomentumLevel lam edge x ≤ ξ} β ∧
        ∃ χ : ℝ, 0 < χ ∧ spectralLevelGradient lam edge β = χ • v := by
  obtain ⟨D⟩ := exists_spectralLevelBodyData lam edge hlam hvalue hstationary hpositive
  refine ⟨D.radius, D.quadraticConstant * D.radius ^ 2, D.radius_pos,
    mul_pos D.quadraticConstant_pos (sq_pos_of_pos D.radius_pos), ?_⟩
  intro ξ hξ hξr
  obtain ⟨hc, hs, hz, _⟩ := D.body_properties hξ hξr
  exact ⟨hc, hs, hz, fun v hv => D.exists_unique_support_point hξ hξr v hv⟩

end Maxwell.Green
