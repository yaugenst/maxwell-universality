import Maxwell.Continuum.BoxModesPEC
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! L² convergence of uniformly dominated cutoff approximants. -/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open Filter MeasureTheory
open scoped Topology InnerProductSpace

theorem l2_norm_sq_eq_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (u : Lp ℂ 2 μ) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner u u)]
  simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]

/-- Dominated convergence in the actual complex L² norm. Eventual equality
at each point is the exact property of shrinking interior cutoffs. -/
theorem tendsto_L2_of_ae_eventually_eq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (F : ℕ → Lp ℂ 2 μ) (f : Lp ℂ 2 μ) (B : α → ℝ)
    (hB : Integrable (fun x => B x ^ 2) μ)
    (hF : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ B x)
    (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ B x)
    (hlim : ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop, F n x = f x) :
    Tendsto F atTop (𝓝 f) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun x => ‖F n x - f x‖ ^ 2) μ :=
    ((Lp.aestronglyMeasurable (F n)).sub (Lp.aestronglyMeasurable f)).norm.pow 2
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖‖F n x - f x‖ ^ 2‖ ≤ 4 * B x ^ 2 := by
    filter_upwards [hF n, hf] with x hn hx
    have hBpos : 0 ≤ B x := (norm_nonneg _).trans hx
    have hdiff : ‖F n x - f x‖ ≤ 2 * B x :=
      (norm_sub_le _ _).trans (by linarith)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (F n x - f x)]
  have hpoint : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => ‖F n x - f x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    apply tendsto_congr' (hx.mono fun n hn => by rw [hn, sub_self, norm_zero, zero_pow (by omega)]) |>.mpr
    exact tendsto_const_nhds
  have hint := tendsto_integral_of_dominated_convergence (fun x => 4 * B x ^ 2)
    hmeas (hB.const_mul 4) hbound hpoint
  simp only [integral_zero] at hint
  have heq (n : ℕ) : ‖F n - f‖ ^ 2 = ∫ x, ‖F n x - f x‖ ^ 2 ∂μ := by
    rw [l2_norm_sq_eq_integral μ]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (F n) f] with x hx
    rw [hx]
    rfl
  have hnormsq : Tendsto (fun n => ‖F n - f‖ ^ 2) atTop (𝓝 (0 : ℝ)) :=
    hint.congr (fun n => (heq n).symm)
  have hnorm := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hnormsq
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at hnorm
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

instance openBox_volume_finite (N : Fin 3 → ℝ) :
    IsFiniteMeasure (volume.restrict (openBox N)) := by
  rw [← (cubePoint_measurePreserving N).map_eq]
  infer_instance

theorem square_integrable_box_bound (N : Fin 3 → ℝ) (K : ℝ) :
    Integrable (fun x : Point => ((openBox N).indicator (fun _ => K) x) ^ 2) volume := by
  have he : (fun x : Point => ((openBox N).indicator (fun _ => K) x) ^ 2) =
      (openBox N).indicator (fun _ => K ^ 2) := by
    funext x
    by_cases hx : x ∈ openBox N <;> simp [Set.indicator, hx]
  rw [he, integrable_indicator_iff (isOpen_openBox N).measurableSet]
  exact integrable_const _

#print axioms tendsto_L2_of_ae_eventually_eq

end Maxwell.Continuum.BoxModes
