import Maxwell.Green.Support
import Maxwell.Green.QuadraticControl

/-! Support geometry for a spectral sublevel cut out in a local chart.
The artificial chart boundary is excluded by the proved quadratic bound. -/

noncomputable section

namespace Maxwell.Green

open Set Filter Metric
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem local_support_on_level
    (F : E → ℝ) {r ε : ℝ} {v β : E} (hv : v ≠ 0)
    (hβ : β ∈ ball (0 : E) r) (hlevel : F β ≤ ε) (hF : ContinuousAt F β)
    (hmax : IsMaxOn (fun x => ⟪v, x⟫_ℝ)
      {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε} β) : F β = ε := by
  by_contra hne
  have hlt : F β < ε := lt_of_le_of_ne hlevel hne
  have hball : ∀ᶠ x in 𝓝 β, x ∈ ball (0 : E) r := isOpen_ball.mem_nhds hβ
  have he : ∀ᶠ x in 𝓝 β, x ∈ ball (0 : E) r ∧ F x < ε :=
    hball.and (hF.eventually (gt_mem_nhds hlt))
  apply support_not_mem_interior hv hmax
  apply mem_interior_iff_mem_nhds.mpr
  exact he.mono fun x hx => ⟨ball_subset_closedBall hx.1, hx.2.le⟩

theorem local_support_gradient_positive_multiple
    (F : E → ℝ) {r ε : ℝ} {v β g : E} (hv : v ≠ 0)
    (hβ : β ∈ ball (0 : E) r) (hlevel : F β = ε)
    (hconv : Convex ℝ {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε})
    (hzero : (0 : E) ∈ interior {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε})
    (hmax : IsMaxOn (fun x => ⟪v, x⟫_ℝ)
      {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε} β)
    (hderiv : HasStrictFDerivAt F (innerSL ℝ g) β) (hgzero : g ≠ 0) :
    ∃ χ : ℝ, 0 < χ ∧ g = χ • v := by
  let s := {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε}
  have hball : ∀ᶠ x in 𝓝 β, x ∈ ball (0 : E) r := isOpen_ball.mem_nhds hβ
  have hmaxlevel : IsLocalMaxOn (fun x => ⟪v, x⟫_ℝ) {x | F x = F β} β := by
    filter_upwards [hball.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with x hx hxlevel
    exact hmax ⟨ball_subset_closedBall hx, (hxlevel.trans hlevel).le⟩
  have hextr : IsLocalExtrOn (fun x => ⟪v, x⟫_ℝ) {x | F x = F β} β := Or.inr hmaxlevel
  obtain ⟨a, b, hab, hlin⟩ :=
    hextr.exists_multipliers_of_hasStrictFDerivAt_1d hderiv (innerSL ℝ v).hasStrictFDerivAt
  have hpoint (x : E) : a * ⟪g, x⟫_ℝ + b * ⟪v, x⟫_ℝ = 0 :=
    congrArg (fun L : E →L[ℝ] ℝ => L x) hlin
  have ha : a ≠ 0 := by
    intro ha
    have hp := hpoint v
    rw [ha, zero_mul, zero_add, real_inner_self_eq_norm_sq] at hp
    have hb : b = 0 := (mul_eq_zero.mp hp).resolve_right
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))
    exact hab (by simp [ha, hb])
  have hg : g = (-b / a) • v := by
    apply ext_inner_right ℝ
    intro x
    rw [real_inner_smul_left, div_mul_eq_mul_div]
    apply (eq_div_iff ha).mpr
    nlinarith [hpoint x]
  have hrate := support_pairing_pos hzero hv hmax
  have hβs : β ∈ s := ⟨ball_subset_closedBall hβ, hlevel.le⟩
  have hFmax : IsMaxOn F s β := fun x hx => hx.2.trans_eq hlevel.symm
  have hsegment : segment ℝ β (0 : E) ⊆ s :=
    hconv.segment_subset hβs (interior_subset hzero)
  have htangent := sub_mem_posTangentConeAt_of_segment_subset hsegment
  have hnormal := hFmax.isLocalMaxOn.hasFDerivWithinAt_nonpos
    hderiv.hasFDerivAt.hasFDerivWithinAt htangent
  simp only [zero_sub, innerSL_apply_apply, inner_neg_right] at hnormal
  have hχnonneg : 0 ≤ -b / a := by
    rw [hg, real_inner_smul_left] at hnormal
    nlinarith
  have hχne : -b / a ≠ 0 := by
    intro hz
    exact hgzero (by simpa only [hz, zero_smul] using hg)
  exact ⟨-b / a, lt_of_le_of_ne hχnonneg hχne.symm, hg⟩

/-- The actual compact local body has one support point, lying on the
physical energy surface with the positive normal equation. -/
theorem exists_unique_regular_local_support_point
    (F : E → ℝ) (g : E → E) (r ε : ℝ)
    (hcompact : IsCompact {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε})
    (hstrict : StrictConvex ℝ {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε})
    (hzero : (0 : E) ∈ interior {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε})
    (hinside : {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε} ⊆ ball (0 : E) r)
    (hderiv : ∀ x ∈ ball (0 : E) r, HasStrictFDerivAt F (innerSL ℝ (g x)) x)
    (hregular : ∀ x ∈ ball (0 : E) r, F x = ε → g x ≠ 0)
    (v : E) (hv : v ≠ 0) :
    ∃! β : E, β ∈ ball (0 : E) r ∧ F β = ε ∧
      IsMaxOn (fun x => ⟪v, x⟫_ℝ) {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε} β ∧
      ∃ χ : ℝ, 0 < χ ∧ g β = χ • v := by
  obtain ⟨β, hβ, hmax⟩ := hcompact.exists_isMaxOn ⟨0, interior_subset hzero⟩
    (innerSL ℝ v).continuous.continuousOn
  have hβball := hinside hβ
  have hlevel := local_support_on_level F hv hβball hβ.2 (hderiv β hβball).continuousAt hmax
  refine ⟨β, ⟨hβball, hlevel, hmax, ?_⟩, ?_⟩
  · exact local_support_gradient_positive_multiple F hv hβball hlevel hstrict.convex hzero
      hmax (hderiv β hβball) (hregular β hβball hlevel)
  · intro γ hγ
    exact support_unique hstrict hv ⟨ball_subset_closedBall hγ.1, hγ.2.1.le⟩ hβ hγ.2.2.1 hmax

omit [CompleteSpace E] in
/-- The enclosing ellipsoid comparison applies to the actual local body.
The inner competitor is proved to stay in the chart from its operator-norm
radius, so no global spectral extension is required. -/
theorem local_support_rate_bounds
    (F : E → ℝ) (P Q : E →L[ℝ] E)
    (hPQ : ∀ x, P (Q x) = x) (hQP : ∀ x, Q (P x) = x)
    (hsym : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (r ε a b : ℝ) (hε : 0 ≤ ε) (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x ∈ closedBall (0 : E) r, a * ‖Q x‖ ^ 2 / 2 ≤ F x)
    (hupper : ∀ x ∈ closedBall (0 : E) r, F x ≤ b * ‖Q x‖ ^ 2 / 2)
    (hfit : ‖P‖ * Real.sqrt (2 * ε / b) ≤ r)
    (v β : E) (hβ : β ∈ closedBall (0 : E) r ∧ F β ≤ ε)
    (hmax : IsMaxOn (fun x => inner ℝ v x)
      {x | x ∈ closedBall (0 : E) r ∧ F x ≤ ε} β) :
    Real.sqrt (2 * ε / b) * ‖P v‖ ≤ inner ℝ v β ∧
      inner ℝ v β ≤ Real.sqrt (2 * ε / a) * ‖P v‖ := by
  apply support_rate_bounds_of_ellipsoids P Q hPQ hQP hsym hβ hmax
    _ _ (Real.sqrt_nonneg _)
  · intro x hx
    have hxr : x ∈ closedBall (0 : E) r := by
      rw [mem_closedBall, dist_zero_right, ← hPQ x]
      exact (P.le_opNorm (Q x)).trans ((mul_le_mul_of_nonneg_left hx (norm_nonneg P)).trans hfit)
    refine ⟨hxr, (hupper x hxr).trans ?_⟩
    have hsq := Real.sq_sqrt (show 0 ≤ 2 * ε / b by positivity)
    have hn := norm_nonneg (Q x)
    have hs := Real.sqrt_nonneg (2 * ε / b)
    have hx₂ : ‖Q x‖ ^ 2 ≤ 2 * ε / b := by nlinarith
    have hm := (le_div_iff₀ hb).mp hx₂
    nlinarith
  · intro x hx
    have hsqa := Real.sq_sqrt (show 0 ≤ 2 * ε / a by positivity)
    have hs : ‖Q x‖ ^ 2 ≤ 2 * ε / a := by
      apply (le_div_iff₀ ha).mpr
      nlinarith [hlower x hx.1, hx.2]
    nlinarith [norm_nonneg (Q x), Real.sqrt_nonneg (2 * ε / a)]

end Maxwell.Green
