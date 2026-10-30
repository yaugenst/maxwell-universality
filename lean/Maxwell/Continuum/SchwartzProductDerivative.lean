import Maxwell.Continuum.SchwartzMultiplier
import Maxwell.Continuum.TranslationH1

/-! Exact distributional Leibniz rules for smooth compact cutoffs, with
actual L² weak derivatives and operator norm bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.SchwartzMultiplier

open MeasureTheory FourierSobolev
open scoped SchwartzMap

theorem partialSchwartz_product (j : Fin 3) (θ φ : SchwartzMap Space ℂ) :
    partialSchwartz j (SchwartzMap.smulLeftCLM ℂ θ φ) =
      SchwartzMap.smulLeftCLM ℂ (partialSchwartz j θ) φ+
        SchwartzMap.smulLeftCLM ℂ θ (partialSchwartz j φ) := by
  ext x
  change fderiv ℝ (SchwartzMap.smulLeftCLM ℂ θ φ) x (coordinateDirection j) = _
  rw [SchwartzMap.smulLeftCLM_apply θ.hasTemperateGrowth]
  have hθ := (θ.differentiableAt (x := x)).hasFDerivAt
  have hφ := (φ.differentiableAt (x := x)).hasFDerivAt
  have hm := hθ.mul hφ
  change (fderiv ℝ (⇑θ*⇑φ) x) (coordinateDirection j) = _
  rw [hm.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul,
    SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (partialSchwartz j θ).hasTemperateGrowth]
  change θ x*(partialSchwartz j φ x)+φ x*(partialSchwartz j θ x) =
    partialSchwartz j θ x*φ x+θ x*(partialSchwartz j φ x)
  ring

theorem partialDistribution_product (j : Fin 3) (θ : SchwartzMap Space ℂ)
    (F : ScalarDistribution) :
    partialDistribution j (TemperedDistribution.smulLeftCLM ℂ θ F) =
      TemperedDistribution.smulLeftCLM ℂ (partialSchwartz j θ) F+
        TemperedDistribution.smulLeftCLM ℂ θ (partialDistribution j F) := by
  ext φ
  simp only [partialDistribution, LineDeriv.lineDerivOpCLM_apply,
    TemperedDistribution.lineDerivOp_apply_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    add_apply, map_neg]
  change -F (SchwartzMap.smulLeftCLM ℂ θ (partialSchwartz j φ)) =
    F (SchwartzMap.smulLeftCLM ℂ (partialSchwartz j θ) φ)-
      F (partialSchwartz j (SchwartzMap.smulLeftCLM ℂ θ φ))
  rw [partialSchwartz_product, map_add]
  abel

theorem scalar_distribution_add (u v : ScalarL2) :
    Lp.toTemperedDistribution (u+v) = Lp.toTemperedDistribution u+Lp.toTemperedDistribution v :=
  map_add (Lp.toTemperedDistributionCLM ℂ (volume : Measure Space) 2) u v

def h1Product (θ : SchwartzMap Space ℂ) {f : FieldL2} (Df : H1Data f) :
    H1Data (field θ f) where
  derivative j := field (partialSchwartz j θ) f+field θ (Df.derivative j)
  weak_derivative j k := by
    simp only [field_apply, PiLp.add_apply]
    rw [scalar_distribution, partialDistribution_product, Df.weak_derivative,
      scalar_distribution_add, scalar_distribution, scalar_distribution]

theorem h1Product_derivative_bound {C C₁ : ℝ} (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
    (θ : SchwartzMap Space ℂ) (hθ : ∀ x, ‖θ x‖ ≤ C)
    (hθ₁ : ∀ j x, ‖partialSchwartz j θ x‖ ≤ C₁)
    {f : FieldL2} (Df : H1Data f) (j : Fin 3) :
    ‖(h1Product θ Df).derivative j‖ ≤ C₁*‖f‖+C*‖Df.derivative j‖ :=
  (norm_add_le _ _).trans (add_le_add
    (field_norm_le hC₁ (partialSchwartz j θ) (hθ₁ j) f)
    (field_norm_le hC θ hθ (Df.derivative j)))

#print axioms partialDistribution_product
#print axioms h1Product

end Maxwell.Continuum.SchwartzMultiplier
