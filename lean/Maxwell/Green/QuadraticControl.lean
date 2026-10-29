import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Quantitative quadratic control derived from second derivatives.

The one-dimensional argument integrates monotonicity twice after removing
the model quadratic. Restriction to lines gives the finite-dimensional
Taylor bound; positive quadratic remainders then imply strict convexity.
-/

noncomputable section

namespace Maxwell.Green

open Set Filter
open scoped Topology

/-- A second derivative lower bound on a unit segment gives the exact
quadratic Taylor lower bound, including its first derivative term. -/
theorem quadratic_taylor_lower_unit
    (f f' f'' : ℝ → ℝ) (c : ℝ)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f' (f'' t) t)
    (hlower : ∀ t ∈ Icc (0 : ℝ) 1, 2 * c ≤ f'' t) :
    f 0 + f' 0 + c ≤ f 1 := by
  let g : ℝ → ℝ := fun t => f t - f 0 - t * f' 0 - c * t ^ 2
  let g' : ℝ → ℝ := fun t => f' t - f' 0 - 2 * c * t
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (g' t) t := by
    have hlin : HasDerivAt (fun u => f u - f 0 - u * f' 0) (f' t - f' 0) t := by
      simpa only [id_eq, one_mul] using ((hf t ht).sub_const (f 0)).fun_sub
        ((hasDerivAt_id t).mul_const (f' 0))
    have hquad : HasDerivAt (fun u : ℝ => c * u ^ 2) (2 * c * t) t := by
      convert (hasDerivAt_pow 2 t).const_mul c using 1
      ring
    exact hlin.fun_sub hquad
  have hg' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt g' (f'' t - 2 * c) t := by
    simpa only [g', id_eq, mul_one] using ((hf' t ht).sub_const (f' 0)).fun_sub
      ((hasDerivAt_id t).const_mul (2 * c))
  have hmono' : MonotoneOn g' (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun t ht => (hg' t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg' t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    exact sub_nonneg.mpr (hlower t (interior_subset ht))
  have hg'nonneg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ g' t := by
    have h := hmono' (by simp) ht ht.1
    simpa only [g', zero_mul, mul_zero, sub_self, sub_zero] using h
  have hmono : MonotoneOn g (Icc (0 : ℝ) 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hg'nonneg t (interior_subset ht))
  have h := hmono (by simp) (by simp) (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [g] at h
  nlinarith

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Restricting the Fréchet Hessian to a segment gives the quantitative
multivariate Taylor inequality. -/
theorem quadratic_taylor_lower_segment
    (F : E → ℝ) (DF : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (x y : E) (c : ℝ)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt F (DF (x + t • y)) (x + t • y))
    (hDF : ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt DF (H (x + t • y)) (x + t • y))
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, 2 * c * ‖y‖ ^ 2 ≤ H (x + t • y) y y) :
    F x + DF x y + c * ‖y‖ ^ 2 ≤ F (x + y) := by
  have hline (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • y) y t := by
    simpa using ((hasDerivAt_id t).smul_const y).const_add x
  have hfirst (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => F (x + t • y)) (DF (x + t • y) y) t :=
    (hF t ht).comp_hasDerivAt t (hline t)
  have hsecond (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => DF (x + t • y) y) (H (x + t • y) y y) t := by
    have hmap : HasDerivAt (fun t : ℝ => DF (x + t • y)) (H (x + t • y) y) t :=
      (hDF t ht).comp_hasDerivAt t (hline t)
    have h := hmap.clm_apply (hasDerivAt_const t y)
    simpa using h
  have h := quadratic_taylor_lower_unit
    (fun t => F (x + t • y)) (fun t => DF (x + t • y) y)
    (fun t => H (x + t • y) y y) (c * ‖y‖ ^ 2) hfirst hsecond
    (fun t ht => by nlinarith [hH t ht])
  simpa only [zero_smul, add_zero, one_smul] using h

/-- Positive Hessian control on a convex domain gives quadratic first-order
control between every two points in that domain. -/
theorem quadratic_taylor_lower_on
    {s : Set E} (hs : Convex ℝ s)
    (F : E → ℝ) (DF : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ)
    (hF : ∀ x ∈ s, HasFDerivAt F (DF x) x)
    (hDF : ∀ x ∈ s, HasFDerivAt DF (H x) x)
    (hH : ∀ x ∈ s, ∀ y, 2 * c * ‖y‖ ^ 2 ≤ H x y y)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    F x + DF x (y - x) + c * ‖y - x‖ ^ 2 ≤ F y := by
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • (y - x) ∈ s := by
    have h := hs hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
    convert h using 1
    module
  have h := quadratic_taylor_lower_segment F DF H x (y - x) c
    (fun t ht => hF _ (hseg t ht)) (fun t ht => hDF _ (hseg t ht))
    (fun t ht => hH _ (hseg t ht) _)
  simpa only [add_sub_cancel] using h

/-- At a stationary zero, the Hessian estimate supplies actual local
quadratic coercivity. -/
theorem quadratic_coercivity_on
    {s : Set E} (hs : Convex ℝ s) (hzero : (0 : E) ∈ s)
    (F : E → ℝ) (DF : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ)
    (hF : ∀ x ∈ s, HasFDerivAt F (DF x) x)
    (hDF : ∀ x ∈ s, HasFDerivAt DF (H x) x)
    (hH : ∀ x ∈ s, ∀ y, 2 * c * ‖y‖ ^ 2 ≤ H x y y)
    (hFzero : F 0 = 0) (hDFzero : DF 0 = 0) {x : E} (hx : x ∈ s) :
    c * ‖x‖ ^ 2 ≤ F x := by
  have h := quadratic_taylor_lower_on hs F DF H c hF hDF hH hzero hx
  simpa only [hFzero, hDFzero, zero_apply, zero_add, sub_zero] using h

/-- A positive quadratic first-order remainder forces strict convexity.
This implication does not take convexity of the function as a premise. -/
theorem strictConvexOn_of_quadratic_lower
    {s : Set E} (hs : Convex ℝ s) (F : E → ℝ) (DF : E → E →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c)
    (hlower : ∀ x ∈ s, ∀ y ∈ s,
      F x + DF x (y - x) + c * ‖y - x‖ ^ 2 ≤ F y) :
    StrictConvexOn ℝ s F := by
  refine ⟨hs, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  let z : E := a • x + b • y
  have hz : z ∈ s := hs hx hy ha.le hb.le hab
  have h₁ := mul_le_mul_of_nonneg_left (hlower z hz x hx) ha.le
  have h₂ := mul_le_mul_of_nonneg_left (hlower z hz y hy) hb.le
  have hvec : a • (x - z) + b • (y - z) = 0 := by
    calc
      _ = a • x + b • y - (a + b) • z := by module
      _ = 0 := by rw [hab, one_smul]; exact sub_self z
  have hlin : a * DF z (x - z) + b * DF z (y - z) = 0 := by
    have h := congrArg (DF z) hvec
    simpa only [map_add, map_smul, smul_eq_mul, map_zero] using h
  have hnorm : 0 < a * ‖x - z‖ ^ 2 + b * ‖y - z‖ ^ 2 := by
    by_cases hxz : x = z
    · have hyz : y - z ≠ 0 := sub_ne_zero.mpr (by intro h; exact hxy (hxz.trans h.symm))
      have hp := mul_pos hb (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hyz))
      nlinarith [mul_nonneg ha.le (sq_nonneg ‖x - z‖)]
    · have hxz' : x - z ≠ 0 := sub_ne_zero.mpr hxz
      have hp := mul_pos ha (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hxz'))
      nlinarith [mul_nonneg hb.le (sq_nonneg ‖y - z‖)]
  change F z < a * F x + b * F y
  have hsumF : a * F z + b * F z = F z := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_pos hc hnorm]

/-- Positive Hessian control directly gives strict convexity. -/
theorem strictConvexOn_of_hessian_lower
    {s : Set E} (hs : Convex ℝ s)
    (F : E → ℝ) (DF : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (c : ℝ) (hc : 0 < c)
    (hF : ∀ x ∈ s, HasFDerivAt F (DF x) x)
    (hDF : ∀ x ∈ s, HasFDerivAt DF (H x) x)
    (hH : ∀ x ∈ s, ∀ y, 2 * c * ‖y‖ ^ 2 ≤ H x y y) :
    StrictConvexOn ℝ s F :=
  strictConvexOn_of_quadratic_lower hs F DF c hc
    (fun _ hx _ hy => quadratic_taylor_lower_on hs F DF H c hF hDF hH hx hy)

/-- Nonzero level points have nonzero derivative, with no separate
regular-boundary assumption needed. -/
theorem derivative_ne_zero_of_quadratic_lower
    {s : Set E} (hzero : (0 : E) ∈ s)
    (F : E → ℝ) (DF : E → E →L[ℝ] ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hlower : ∀ x ∈ s, ∀ y ∈ s,
      F x + DF x (y - x) + c * ‖y - x‖ ^ 2 ≤ F y)
    {x : E} (hx : x ∈ s) (hlevel : F 0 < F x) : DF x ≠ 0 := by
  intro hzeroDF
  have h := hlower x hx 0 hzero
  rw [hzeroDF, zero_apply] at h
  nlinarith [mul_nonneg hc (sq_nonneg ‖(0 : E) - x‖)]

/-- The operator norm of a bilinear form controls its diagonal values. -/
theorem norm_bilinear_diagonal_le (B : E →L[ℝ] E →L[ℝ] ℝ) (y : E) :
    ‖B y y‖ ≤ ‖B‖ * ‖y‖ ^ 2 := by
  calc
    ‖B y y‖ ≤ ‖B y‖ * ‖y‖ := (B y).le_opNorm y
    _ ≤ (‖B‖ * ‖y‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right (B.le_opNorm y) (norm_nonneg y)
    _ = _ := by ring

/-- In finite dimension (or any proper normed space), pointwise positive
definiteness supplies a uniform positive quadratic constant. Compactness
of the unit sphere proves the constant exists. -/
theorem positive_bilinear_has_uniform_lower [ProperSpace E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ y, y ≠ 0 → 0 < B y y) :
    ∃ c : ℝ, 0 < c ∧ ∀ y, c * ‖y‖ ^ 2 ≤ B y y := by
  have hcont : Continuous (fun y => B y y) := B.continuous.clm_apply continuous_id
  obtain ⟨c, hc, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le'
    hcont.continuousOn (fun y hy => hB y (by
      have hynorm : ‖y‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hy
      intro hzero
      simp only [hzero, norm_zero] at hynorm
      norm_num at hynorm))
  refine ⟨c, hc, ?_⟩
  intro y
  by_cases hy : y = 0
  · simp [hy]
  · have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    let u : E := ‖y‖⁻¹ • y
    have hu : u ∈ Metric.sphere (0 : E) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]
    have hscale : B u u = ‖y‖⁻¹ * (‖y‖⁻¹ * B y y) := by
      simp only [u, map_smul, smul_apply, smul_eq_mul]
    have h := mul_le_mul_of_nonneg_left (hmin u hu) (sq_nonneg ‖y‖)
    rw [hscale] at h
    have hcancel : ‖y‖ ^ 2 * (‖y‖⁻¹ * (‖y‖⁻¹ * B y y)) = B y y := by
      field_simp
    rw [hcancel] at h
    simpa only [mul_comm] using h

/-- A small operator perturbation preserves a quantitative Hessian lower
bound, simultaneously in every direction. -/
theorem bilinear_lower_of_norm_sub_le
    (Q B : E →L[ℝ] E →L[ℝ] ℝ) (a δ : ℝ)
    (hQ : ∀ y, a * ‖y‖ ^ 2 ≤ Q y y) (hdiff : ‖B - Q‖ ≤ δ) (y : E) :
    (a - δ) * ‖y‖ ^ 2 ≤ B y y := by
  have h := (norm_bilinear_diagonal_le (B - Q) y).trans
    (mul_le_mul_of_nonneg_right hdiff (sq_nonneg ‖y‖))
  change ‖B y y - Q y y‖ ≤ δ * ‖y‖ ^ 2 at h
  rw [Real.norm_eq_abs] at h
  have hl := (abs_le.mp h).1
  nlinarith [hQ y]

/-- Operator-norm continuity of the Hessian turns its positive lower bound
at the origin into a uniform positive lower bound in an actual neighborhood. -/
theorem exists_ball_hessian_lower
    (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hH : Tendsto (fun x => ‖H x - H 0‖) (𝓝 (0 : E)) (𝓝 (0 : ℝ)))
    (c : ℝ) (hc : 0 < c) (hzero : ∀ y, 4 * c * ‖y‖ ^ 2 ≤ H 0 y y) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Metric.ball (0 : E) r,
      ∀ y, 2 * c * ‖y‖ ^ 2 ≤ H x y y := by
  have he : ∀ᶠ x in 𝓝 (0 : E), ‖H x - H 0‖ < 2 * c := by
    exact hH.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 2 * c))
  obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff_ball.mp he
  refine ⟨r, hr, ?_⟩
  intro x hx y
  have h := bilinear_lower_of_norm_sub_le (H 0) (H x) (4 * c) (2 * c)
    hzero (hnear x hx).le y
  convert h using 1
  ring

omit [NormedSpace ℝ E] in
/-- A small closed sublevel cut out inside a fixed ball stays strictly
inside that ball. This prevents artificial boundary points from the chart
cutoff when applying the compact support-point theorem. -/
theorem local_sublevel_subset_ball
    (F : E → ℝ) (r c ε : ℝ) (hr : 0 < r) (hc : 0 < c) (hε : ε < c * r ^ 2)
    (hlower : ∀ x ∈ Metric.closedBall (0 : E) r, c * ‖x‖ ^ 2 ≤ F x) :
    {x | x ∈ Metric.closedBall (0 : E) r ∧ F x ≤ ε} ⊆ Metric.ball (0 : E) r := by
  intro x hx
  have hsq : c * ‖x‖ ^ 2 < c * r ^ 2 := (hlower x hx.1).trans_lt (hx.2.trans_lt hε)
  have hsq' : ‖x‖ ^ 2 < r ^ 2 := (mul_lt_mul_iff_right₀ hc).mp hsq
  exact mem_ball_zero_iff.mpr ((sq_lt_sq₀ (norm_nonneg _) hr.le).mp hsq')

/-- Continuous positive-Hessian local data produce a compact, strictly
convex sublevel body with an interior origin. -/
theorem local_sublevel_body [ProperSpace E]
    (F : E → ℝ) (hF : Continuous F) (r c ε : ℝ)
    (hr : 0 < r) (hc : 0 < c) (hε : F 0 < ε) (hεr : ε < c * r ^ 2)
    (hstrict : StrictConvexOn ℝ (Metric.closedBall (0 : E) r) F)
    (hlower : ∀ x ∈ Metric.closedBall (0 : E) r, c * ‖x‖ ^ 2 ≤ F x) :
    IsCompact {x | x ∈ Metric.closedBall (0 : E) r ∧ F x ≤ ε} ∧
      StrictConvex ℝ {x | x ∈ Metric.closedBall (0 : E) r ∧ F x ≤ ε} ∧
      (0 : E) ∈ interior {x | x ∈ Metric.closedBall (0 : E) r ∧ F x ≤ ε} := by
  let s := {x | x ∈ Metric.closedBall (0 : E) r ∧ F x ≤ ε}
  have hinside : s ⊆ Metric.ball (0 : E) r :=
    local_sublevel_subset_ball F r c ε hr hc hεr hlower
  have hopen : IsOpen (Metric.ball (0 : E) r ∩ {x | F x < ε}) :=
    Metric.isOpen_ball.inter (isOpen_Iio.preimage hF)
  have hsub : Metric.ball (0 : E) r ∩ {x | F x < ε} ⊆ s := by
    intro x hx
    exact ⟨Metric.ball_subset_closedBall hx.1, hx.2.le⟩
  have hinterior : Metric.ball (0 : E) r ∩ {x | F x < ε} ⊆ interior s :=
    interior_maximal hsub hopen
  refine ⟨(isCompact_closedBall (0 : E) r).inter_right (isClosed_Iic.preimage hF), ?_, ?_⟩
  · intro x hx y hy hxy a b ha hb hab
    apply hinterior
    constructor
    · exact convex_ball (0 : E) r (hinside hx) (hinside hy) ha.le hb.le hab
    · have hlt := hstrict.2 hx.1 hy.1 hxy ha hb hab
      have hupper : a * F x + b * F y ≤ ε := by
        have h₁ := mul_le_mul_of_nonneg_left hx.2 ha.le
        have h₂ := mul_le_mul_of_nonneg_left hy.2 hb.le
        have hsum : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
        linarith
      exact hlt.trans_le hupper
  · apply hinterior
    exact ⟨Metric.mem_ball_self hr, hε⟩

/-- The local sublevel body's compactness, strict convexity, interior origin,
and regular level surface all follow from derivative/Hessian data. -/
theorem local_sublevel_body_of_hessian [ProperSpace E]
    (F : E → ℝ) (DF : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (hcont : Continuous F)
    (r c ε : ℝ) (hr : 0 < r) (hc : 0 < c) (hε : 0 < ε) (hεr : ε < c * r ^ 2)
    (hF : ∀ x ∈ Metric.closedBall (0 : E) r, HasFDerivAt F (DF x) x)
    (hDF : ∀ x ∈ Metric.closedBall (0 : E) r, HasFDerivAt DF (H x) x)
    (hH : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ y, 2 * c * ‖y‖ ^ 2 ≤ H x y y)
    (hFzero : F 0 = 0) (hDFzero : DF 0 = 0) :
    IsCompact {x | x ∈ Metric.closedBall (0 : E) r ∧ F x ≤ ε} ∧
      StrictConvex ℝ {x | x ∈ Metric.closedBall (0 : E) r ∧ F x ≤ ε} ∧
      (0 : E) ∈ interior {x | x ∈ Metric.closedBall (0 : E) r ∧ F x ≤ ε} ∧
      ∀ x ∈ Metric.closedBall (0 : E) r, F x = ε → DF x ≠ 0 := by
  have hzero : (0 : E) ∈ Metric.closedBall (0 : E) r := Metric.mem_closedBall_self hr.le
  have hstrict := strictConvexOn_of_hessian_lower (convex_closedBall (0 : E) r)
    F DF H c hc hF hDF hH
  have hlower := fun x hx => quadratic_coercivity_on (convex_closedBall (0 : E) r) hzero
    F DF H c hF hDF hH hFzero hDFzero (x := x) hx
  obtain ⟨hcompact, hconvex, hinterior⟩ := local_sublevel_body F hcont r c ε hr hc
    (by simpa only [hFzero] using hε) hεr hstrict hlower
  refine ⟨hcompact, hconvex, hinterior, ?_⟩
  intro x hx hlevel
  exact derivative_ne_zero_of_quadratic_lower hzero F DF c hc.le
    (fun _ hy _ hz => quadratic_taylor_lower_on (convex_closedBall (0 : E) r)
      F DF H c hF hDF hH hy hz) hx (by simpa only [hFzero, hlevel] using hε)

/-- Positive definite Hessian at a stationary zero, with local twice
differentiability and operator-norm continuous Hessian, supplies one fixed
chart in which every sufficiently small positive sublevel is compact,
strictly convex, and regular. The neighborhood and constants are obtained
in the proof, rather than included among the assumptions. -/
theorem exists_positive_hessian_sublevel_family [ProperSpace E]
    (F : E → ℝ) (DF : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (hcont : Continuous F)
    (hderiv : ∀ᶠ x in 𝓝 (0 : E), HasFDerivAt F (DF x) x ∧ HasFDerivAt DF (H x) x)
    (hHcont : Tendsto (fun x => ‖H x - H 0‖) (𝓝 (0 : E)) (𝓝 (0 : ℝ)))
    (hpos : ∀ y, y ≠ 0 → 0 < H 0 y y)
    (hFzero : F 0 = 0) (hDFzero : DF 0 = 0) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε < c * r ^ 2 →
      IsCompact {x | x ∈ Metric.closedBall (0 : E) r ∧ F x ≤ ε} ∧
      StrictConvex ℝ {x | x ∈ Metric.closedBall (0 : E) r ∧ F x ≤ ε} ∧
      (0 : E) ∈ interior {x | x ∈ Metric.closedBall (0 : E) r ∧ F x ≤ ε} ∧
      ∀ x ∈ Metric.closedBall (0 : E) r, F x = ε → DF x ≠ 0 := by
  obtain ⟨a, ha, hlower⟩ := positive_bilinear_has_uniform_lower (H 0) hpos
  let c : ℝ := a / 4
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨rH, hrH, hnearH⟩ := exists_ball_hessian_lower H hHcont c hc
    (fun y => by dsimp [c]; nlinarith [hlower y])
  obtain ⟨rD, hrD, hnearD⟩ := Metric.eventually_nhds_iff_ball.mp hderiv
  let r : ℝ := min rH rD / 2
  have hmin : 0 < min rH rD := lt_min hrH hrD
  have hr : 0 < r := by dsimp [r]; positivity
  have hrH' : r < rH := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hrD' : r < rD := (half_lt_self hmin).trans_le (min_le_right _ _)
  have hinsideH : Metric.closedBall (0 : E) r ⊆ Metric.ball (0 : E) rH := by
    intro x hx
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx).trans_lt hrH')
  have hinsideD : Metric.closedBall (0 : E) r ⊆ Metric.ball (0 : E) rD := by
    intro x hx
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx).trans_lt hrD')
  refine ⟨r, c, hr, hc, ?_⟩
  intro ε hε hεr
  exact local_sublevel_body_of_hessian F DF H hcont r c ε hr hc hε hεr
    (fun x hx => (hnearD x (hinsideD hx)).1)
    (fun x hx => (hnearD x (hinsideD hx)).2)
    (fun x hx => hnearH x (hinsideH hx)) hFzero hDFzero

end NormedSpace

end Maxwell.Green
