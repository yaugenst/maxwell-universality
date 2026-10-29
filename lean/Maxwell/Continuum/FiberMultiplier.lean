import Maxwell.Continuum.BlochUnitary
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-! Measurable bounded operator fields act on actual Hilbert-valued L²
classes. This supplies the direct-integral cutoff operator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FiberMultiplier

open MeasureTheory Filter

variable {X H : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure Data (μ : Measure X) (C : ℝ) where
  operator : X → H →L[ℂ] H
  measurable : AEStronglyMeasurable operator μ
  nonneg : 0 ≤ C
  bound : ∀ x, ‖operator x‖ ≤ C

namespace Data

variable {μ : Measure X} {C : ℝ} (D : Data (H := H) μ C)

theorem action_measurable (f : Lp H 2 μ) :
    AEStronglyMeasurable (fun x => D.operator x (f x)) μ :=
  (ContinuousLinearMap.id ℂ (H →L[ℂ] H)).aestronglyMeasurable_comp₂
    D.measurable (Lp.aestronglyMeasurable f)

theorem action_bound (f : Lp H 2 μ) (x : X) :
    ‖D.operator x (f x)‖ ≤ C * ‖f x‖ :=
  (D.operator x).le_of_opNorm_le (D.bound x) (f x)

theorem action_memLp (f : Lp H 2 μ) : MemLp (fun x => D.operator x (f x)) 2 μ := by
  apply ((Lp.memLp f).const_smul (C : ℂ)).of_le (D.action_measurable f)
  exact Eventually.of_forall fun x => by
    simpa only [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg D.nonneg] using
      D.action_bound f x

def action (f : Lp H 2 μ) : Lp H 2 μ := (D.action_memLp f).toLp _

theorem action_ae (f : Lp H 2 μ) : D.action f =ᵐ[μ] fun x => D.operator x (f x) :=
  MemLp.coeFn_toLp _

def actionLinear : Lp H 2 μ →ₗ[ℂ] Lp H 2 μ where
  toFun := D.action
  map_add' f g := by
    apply Lp.ext
    filter_upwards [D.action_ae (f+g), D.action_ae f, D.action_ae g,
      Lp.coeFn_add f g, Lp.coeFn_add (D.action f) (D.action g)] with x hfg hf hg ha hb
    simp only [hfg, hb, ha, Pi.add_apply, hf, hg, map_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [D.action_ae (c • f), D.action_ae f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (D.action f)] with x hcf hf ha hb
    change D.action (c • f) x = (c • D.action f) x
    simp only [hcf, hb, ha, Pi.smul_apply, hf, map_smul]

theorem action_norm_le (f : Lp H 2 μ) : ‖D.action f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [D.action_ae f] with x hx
  rw [hx]
  exact D.action_bound f x

def multiplier : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  D.actionLinear.mkContinuous C D.action_norm_le

theorem multiplier_ae (f : Lp H 2 μ) : D.multiplier f =ᵐ[μ] fun x => D.operator x (f x) :=
  D.action_ae f

theorem multiplier_norm_le : ‖D.multiplier‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ D.nonneg D.action_norm_le

theorem multiplier_symmetric (hD : ∀ x, (D.operator x).IsSymmetric) :
    D.multiplier.IsSymmetric := by
  intro f g
  change inner ℂ (D.multiplier f) g = inner ℂ f (D.multiplier g)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [D.multiplier_ae f, D.multiplier_ae g] with x hf hg
  rw [hf, hg]
  exact hD x _ _

theorem multiplier_difference_norm_le {C' B : ℝ} (E : Data (H := H) μ C')
    (hB : 0 ≤ B) (hDE : ∀ x, ‖D.operator x - E.operator x‖ ≤ B) :
    ‖D.multiplier - E.multiplier‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [D.multiplier_ae f, E.multiplier_ae f,
    Lp.coeFn_sub (D.multiplier f) (E.multiplier f)] with x hd he hs
  change ‖(D.multiplier f - E.multiplier f) x‖ ≤ _
  rw [hs]
  simp only [Pi.sub_apply, hd, he]
  exact (D.operator x - E.operator x).le_of_opNorm_le (hDE x) (f x)

end Data
end Maxwell.Continuum.FiberMultiplier
