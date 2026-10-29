import Maxwell.Continuum.WellRayleighLower

/-! Taking pointwise absolute values preserves the L² norm and increases
the Rayleigh form of the actual positive-kernel well operator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Well

open MeasureTheory

def absolute (f : ScalarL2) : ScalarL2 := ((Lp.memLp f).norm.ofReal).toLp _

theorem absolute_ae (f : ScalarL2) : absolute f =ᵐ[volume] fun x => (‖f x‖ : ℂ) :=
  MemLp.coeFn_toLp _

theorem absolute_norm (f : ScalarL2) : ‖absolute f‖ = ‖f‖ := by
  simp only [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [absolute_ae f] with x hx
  rw [hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]

def absoluteAction (f : ScalarL2) (x : Space) : ℝ :=
  ∫ y : Space, wellKernel x y * ‖f y‖

theorem absoluteAction_integrable (f : ScalarL2) (x : Space) :
    Integrable (fun y : Space => wellKernel x y * ‖f y‖) := by
  apply ((wellKernel_integrand (absolute f) x).re).congr
  filter_upwards [absolute_ae f] with y hy
  rw [hy]
  simp

theorem absoluteAction_nonneg (f : ScalarL2) (x : Space) : 0 ≤ absoluteAction f x :=
  integral_nonneg (fun y => mul_nonneg (wellKernel_nonneg x y) (norm_nonneg _))

theorem physicalBirmanSchwinger_absolute_ae (f : ScalarL2) :
    physicalBirmanSchwinger (absolute f) =ᵐ[volume] fun x => (absoluteAction f x : ℂ) := by
  filter_upwards [physicalBirmanSchwinger_kernel_ae (absolute f)] with x hx
  rw [hx, absoluteAction, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [absolute_ae f] with y hy
  rw [hy, Complex.ofReal_mul]

theorem physicalBirmanSchwinger_norm_ae_le_absoluteAction (f : ScalarL2) :
    ∀ᵐ x, ‖physicalBirmanSchwinger f x‖ ≤ absoluteAction f x := by
  filter_upwards [physicalBirmanSchwinger_kernel_ae f] with x hx
  rw [hx]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wellKernel_nonneg x y)])

theorem absolute_energy_ge (f : ScalarL2) :
    RCLike.re (inner ℂ f (physicalBirmanSchwinger f)) ≤
      RCLike.re (inner ℂ (absolute f) (physicalBirmanSchwinger (absolute f))) := by
  rw [L2.inner_def, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) _ _),
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) _ _)]
  apply integral_mono_ae (L2.integrable_inner (𝕜 := ℂ) _ _).re
    (L2.integrable_inner (𝕜 := ℂ) _ _).re
  filter_upwards [absolute_ae f, physicalBirmanSchwinger_absolute_ae f,
    physicalBirmanSchwinger_norm_ae_le_absoluteAction f] with x hx ht hn
  rw [hx, ht, complex_inner_re_ofReal]
  exact (re_inner_le_norm (𝕜 := ℂ) _ _).trans
    (mul_le_mul_of_nonneg_left hn (norm_nonneg _))

end Maxwell.Continuum.Well
