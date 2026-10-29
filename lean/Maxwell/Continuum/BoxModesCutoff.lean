import Maxwell.Continuum.BoxModesPEC
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Explicit smooth interior cutoffs for PEC modes

The transition profile is fixed once and for all. Shrinking face cutoffs
have derivatives of order `δ⁻¹`; the sine factors vanishing on each
tangential face cancel this loss in the curl commutator.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open Filter MeasureTheory
open scoped Topology ContDiff

theorem transition_deriv_zero_of_neg {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [he.deriv_eq, deriv_const]

theorem transition_deriv_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [he.deriv_eq, deriv_const]

theorem transition_deriv_support :
    Function.support (deriv Real.smoothTransition) ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  by_contra hn
  rcases not_and_or.mp hn with hl | hr
  · exact hx (transition_deriv_zero_of_neg (lt_of_not_ge hl))
  · exact hx (transition_deriv_zero_of_one_lt (lt_of_not_ge hr))

/-- A single finite derivative bound for the fixed transition profile. -/
theorem transition_deriv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  have hcompact : HasCompactSupport (deriv Real.smoothTransition) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => by
      by_contra hn
      exact hx (transition_deriv_support hn))
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).continuous_deriv (by simp))
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x => ?_⟩
  exact (hC x).trans (le_max_left _ _)

def intervalCutoff (N δ x : ℝ) : ℝ :=
  Real.smoothTransition (x / δ - 1) * Real.smoothTransition ((N - x) / δ - 1)

theorem intervalCutoff_nonneg (N δ x : ℝ) : 0 ≤ intervalCutoff N δ x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem intervalCutoff_le_one (N δ x : ℝ) : intervalCutoff N δ x ≤ 1 := by
  exact (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _)).trans (by
      simpa only [one_mul] using Real.smoothTransition.le_one ((N - x) / δ - 1))

theorem intervalCutoff_eq_zero_of_le {N δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ δ) :
    intervalCutoff N δ x = 0 := by
  unfold intervalCutoff
  rw [Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ((div_le_one hδ).mpr hx)),
    zero_mul]

theorem intervalCutoff_eq_zero_of_ge {N δ x : ℝ} (hδ : 0 < δ) (hx : N - δ ≤ x) :
    intervalCutoff N δ x = 0 := by
  unfold intervalCutoff
  have hz : Real.smoothTransition ((N - x) / δ - 1) = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (sub_nonpos.mpr ((div_le_one hδ).mpr (by linarith)))
  rw [hz, mul_zero]

theorem intervalCutoff_eq_one {N δ x : ℝ} (hδ : 0 < δ)
    (hl : 2 * δ ≤ x) (hr : x ≤ N - 2 * δ) : intervalCutoff N δ x = 1 := by
  unfold intervalCutoff
  have hlow : 1 ≤ x / δ - 1 := by
    have := (le_div_iff₀ hδ).mpr hl
    linarith
  have hupp : 1 ≤ (N - x) / δ - 1 := by
    have : 2 ≤ (N - x) / δ := (le_div_iff₀ hδ).mpr (by linarith)
    linarith
  rw [Real.smoothTransition.one_of_one_le hlow,
    Real.smoothTransition.one_of_one_le hupp, one_mul]

theorem contDiff_intervalCutoff (N δ : ℝ) : ContDiff ℝ ∞ (intervalCutoff N δ) := by
  exact (Real.smoothTransition.contDiff.comp
    ((contDiff_id.div_const δ).sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp
      (((contDiff_const.sub contDiff_id).div_const δ).sub contDiff_const))

theorem tsupport_intervalCutoff (N : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    tsupport (intervalCutoff N δ) ⊆ Set.Icc δ (N - δ) := by
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  constructor
  · by_contra hn
    exact hx (intervalCutoff_eq_zero_of_le hδ (le_of_not_ge hn))
  · by_contra hn
    exact hx (intervalCutoff_eq_zero_of_ge hδ (le_of_not_ge hn))

theorem hasCompactSupport_intervalCutoff (N : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (intervalCutoff N δ) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (tsupport_intervalCutoff N hδ)

theorem hasDerivAt_intervalCutoff (N δ x : ℝ) :
    HasDerivAt (intervalCutoff N δ)
      ((deriv Real.smoothTransition (x / δ - 1) / δ) *
          Real.smoothTransition ((N - x) / δ - 1) -
        Real.smoothTransition (x / δ - 1) *
          (deriv Real.smoothTransition ((N - x) / δ - 1) / δ)) x := by
  have hs (t : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable
      (by simp)).differentiableAt.hasDerivAt
  have h := ((hs _).comp x (((hasDerivAt_id x).div_const δ).sub_const 1)).mul
    ((hs _).comp x ((((hasDerivAt_const x N).sub (hasDerivAt_id x)).div_const δ).sub_const 1))
  change HasDerivAt (intervalCutoff N δ) _ x at h
  convert h using 1
  dsimp
  ring

/-- On each fixed interior point the cutoffs are eventually exactly one. -/
theorem intervalCutoff_eventually_one (N x : ℝ) (hx : x ∈ Set.Ioo 0 N) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), intervalCutoff N δ x = 1 := by
  have hsmall : 0 < min x (N - x) / 2 :=
    div_pos (lt_min hx.1 (sub_pos.mpr hx.2)) (by norm_num)
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hsmall).filter_mono nhdsWithin_le_nhds] with δ hδ hs
  apply intervalCutoff_eq_one hδ
  · have := (min_le_left x (N - x))
    linarith
  · have := (min_le_right x (N - x))
    linarith

/-- The singular derivative scaling is canceled by a function vanishing
linearly at the adjacent face. -/
theorem transition_deriv_mul_bound (C K δ t v : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hδ : 0 < δ) (hD : ∀ y, |deriv Real.smoothTransition y| ≤ C)
    (hv : |v| ≤ K * |t|) :
    |(deriv Real.smoothTransition (t / δ - 1) / δ) * v| ≤ 2 * C * K := by
  by_cases hz : deriv Real.smoothTransition (t / δ - 1) = 0
  · rw [hz, zero_div, zero_mul, abs_zero]
    positivity
  · have ht := transition_deriv_support hz
    have htlow : 0 ≤ t := by
      have : 1 ≤ t / δ := by linarith [ht.1]
      have := (le_div_iff₀ hδ).mp this
      linarith
    have hthi : t ≤ 2 * δ := by
      apply (div_le_iff₀ hδ).mp
      linarith [ht.2]
    have hv' : |v| ≤ K * (2 * δ) :=
      hv.trans (by rw [abs_of_nonneg htlow]; exact mul_le_mul_of_nonneg_left hthi hK)
    rw [abs_mul, abs_div, abs_of_pos hδ]
    calc
      |deriv Real.smoothTransition (t / δ - 1)| / δ * |v| ≤
          (C / δ) * (K * (2 * δ)) :=
        mul_le_mul (div_le_div_of_nonneg_right (hD _) hδ.le) hv'
          (abs_nonneg _) (div_nonneg hC hδ.le)
      _ = 2 * C * K := by field_simp

/-- Uniform commutator bound for a smooth cutoff times a scalar function
vanishing linearly at both interval endpoints. -/
theorem intervalCutoff_deriv_mul_bound (N C K δ x v : ℝ)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hD : ∀ y, |deriv Real.smoothTransition y| ≤ C)
    (hl : |v| ≤ K * |x|) (hr : |v| ≤ K * |N - x|) :
    |deriv (intervalCutoff N δ) x * v| ≤ 4 * C * K := by
  have ha := transition_deriv_mul_bound C K δ x v hC hK hδ hD hl
  have hb := transition_deriv_mul_bound C K δ (N - x) v hC hK hδ hD hr
  have hθ (y : ℝ) : |Real.smoothTransition y| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  rw [(hasDerivAt_intervalCutoff N δ x).deriv]
  calc
    |(deriv Real.smoothTransition (x / δ - 1) / δ *
          Real.smoothTransition ((N - x) / δ - 1) -
        Real.smoothTransition (x / δ - 1) *
          (deriv Real.smoothTransition ((N - x) / δ - 1) / δ)) * v| =
        |(deriv Real.smoothTransition (x / δ - 1) / δ * v) *
            Real.smoothTransition ((N - x) / δ - 1) -
          (deriv Real.smoothTransition ((N - x) / δ - 1) / δ * v) *
            Real.smoothTransition (x / δ - 1)| := congrArg abs (by ring)
    _ ≤ |(deriv Real.smoothTransition (x / δ - 1) / δ * v) *
            Real.smoothTransition ((N - x) / δ - 1)| +
          |(deriv Real.smoothTransition ((N - x) / δ - 1) / δ * v) *
            Real.smoothTransition (x / δ - 1)| := abs_sub _ _
    _ ≤ (2 * C * K) * 1 + (2 * C * K) * 1 := by
      simpa only [abs_mul] using
        add_le_add (mul_le_mul ha (hθ ((N - x) / δ - 1)) (abs_nonneg _) (by positivity))
          (mul_le_mul hb (hθ (x / δ - 1)) (abs_nonneg _) (by positivity))
    _ = 4 * C * K := by ring

theorem intervalSin_endpoint_bounds (N : ℝ) (hN : 0 < N) (n : ℤ) (x : ℝ) :
    |intervalSin N n x| ≤ |(n : ℝ) * Real.pi / N| * |x| ∧
      |intervalSin N n x| ≤ |(n : ℝ) * Real.pi / N| * |N - x| := by
  constructor
  · simpa only [intervalSin, abs_mul] using
      (Real.abs_sin_le_abs (x := (n : ℝ) * Real.pi / N * x))
  · have hz : Real.sin ((n : ℝ) * Real.pi / N * N) = 0 := by
      rw [div_mul_cancel₀ _ hN.ne', Real.sin_int_mul_pi]
    have h := Real.abs_sin_sub_sin_le
      ((n : ℝ) * Real.pi / N * x) ((n : ℝ) * Real.pi / N * N)
    rw [hz, sub_zero, ← mul_sub, abs_mul, abs_sub_comm x N] at h
    exact h

/-- The exact sine face factors in the PEC modes cancel the cutoff's
inverse-width derivative, uniformly as the cutoff width tends to zero. -/
theorem intervalCutoff_deriv_sin_bound (N : ℝ) (hN : 0 < N) (n : ℤ)
    (C : ℝ) (hC : 0 ≤ C) (hD : ∀ y, |deriv Real.smoothTransition y| ≤ C)
    {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |deriv (intervalCutoff N δ) x * intervalSin N n x| ≤
      4 * C * |(n : ℝ) * Real.pi / N| := by
  obtain ⟨hl, hr⟩ := intervalSin_endpoint_bounds N hN n x
  exact intervalCutoff_deriv_mul_bound N C _ δ x _ hC (abs_nonneg _) hδ hD hl hr

#print axioms transition_deriv_bound
#print axioms intervalCutoff_eventually_one
#print axioms intervalCutoff_deriv_sin_bound

end Maxwell.Continuum.BoxModes
