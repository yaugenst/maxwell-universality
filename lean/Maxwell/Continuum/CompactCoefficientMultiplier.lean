import Maxwell.Continuum.FiberMultiplier
import Mathlib.Topology.ContinuousMap.Compact

/-! Actual multiplication on L² by continuous coefficients evaluated along
a measurable map into a compact space, as a continuous linear map of the
coefficient. This preserves operator-norm analytic dependence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CompactCoefficient

open MeasureTheory Filter

variable {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X}
  (s : X → Y) (hs : Measurable s)

def data (f : C(Y, ℂ)) : FiberMultiplier.Data (H := ℂ) μ ‖f‖ where
  operator x := f (s x) • ContinuousLinearMap.id ℂ ℂ
  measurable := ((f.continuous.measurable.comp hs).aestronglyMeasurable).smul
    aestronglyMeasurable_const
  nonneg := norm_nonneg f
  bound x := by
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one]
    exact f.norm_coe_le_norm (s x)

def multiplier (f : C(Y, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := (data s hs f).multiplier

theorem multiplier_ae (f : C(Y, ℂ)) (u : Lp ℂ 2 μ) :
    multiplier s hs f u =ᵐ[μ] fun x => f (s x) * u x := by
  filter_upwards [(data s hs f).multiplier_ae u] with x hx
  exact hx

theorem multiplier_norm_le (f : C(Y, ℂ)) : ‖multiplier (μ := μ) s hs f‖ ≤ ‖f‖ :=
  (data s hs f).multiplier_norm_le

def coefficientLinear : C(Y, ℂ) →ₗ[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) where
  toFun := multiplier s hs
  map_add' f g := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [multiplier_ae s hs (f + g) u, multiplier_ae s hs f u,
      multiplier_ae s hs g u, Lp.coeFn_add (multiplier s hs f u) (multiplier s hs g u)]
      with x hfg hf hg ha
    change multiplier s hs (f + g) u x = (multiplier s hs f u + multiplier s hs g u) x
    rw [hfg, ha]
    simp only [ContinuousMap.add_apply, Pi.add_apply, hf, hg, add_mul]
  map_smul' c f := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [multiplier_ae s hs (c • f) u, multiplier_ae s hs f u,
      Lp.coeFn_smul c (multiplier s hs f u)] with x hcf hf hc
    change multiplier s hs (c • f) u x = (c • multiplier s hs f u) x
    rw [hcf, hc]
    simp only [ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul, hf]
    ring

def coefficientMap : C(Y, ℂ) →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  (coefficientLinear (μ := μ) s hs).mkContinuous 1 (by
    intro f
    change ‖multiplier s hs f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using multiplier_norm_le (μ := μ) s hs f)

theorem coefficientMap_apply (f : C(Y, ℂ)) : coefficientMap (μ := μ) s hs f = multiplier s hs f := rfl

theorem coefficientMap_norm_le : ‖coefficientMap (μ := μ) s hs‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun f => by
      change ‖multiplier s hs f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using multiplier_norm_le (μ := μ) s hs f)

end Maxwell.Continuum.CompactCoefficient
