import Maxwell.Continuum.KernelTranslation

/-! A genuine L¹ convolution on L², constructed by strong Bochner
integration of translations. No operator-norm continuity of translations
or compactness of the convolution operator is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.KernelIntegral

open MeasureTheory

variable (k : Space → ℂ) (hk : Integrable k)

include hk

theorem convolution_integrable (f : ScalarL2) :
    Integrable (fun y : Space => k y • shift y f) := by
  apply (hk.norm.mul_const ‖f‖).mono'
    (hk.aestronglyMeasurable.smul (shift_continuous f).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun y => by
    change ‖k y • shift y f‖ ≤ ‖k y‖ * ‖f‖
    rw [norm_smul, (shift y).norm_map]

def convolutionLinear : ScalarL2 →ₗ[ℂ] ScalarL2 where
  toFun f := ∫ y : Space, k y • shift y f
  map_add' f g := by
    simp only [map_add, smul_add]
    exact integral_add (convolution_integrable k hk f) (convolution_integrable k hk g)
  map_smul' c f := by
    simp only [map_smul, RingHom.id_apply]
    simp_rw [smul_comm (k _) c]
    exact integral_smul c _

theorem convolutionLinear_norm_le (f : ScalarL2) :
    ‖convolutionLinear k hk f‖ ≤ (∫ y : Space, ‖k y‖) * ‖f‖ := by
  change ‖∫ y : Space, k y • shift y f‖ ≤ _
  calc
    _ ≤ ∫ y : Space, ‖k y • shift y f‖ := norm_integral_le_integral_norm _
    _ = _ := by
      simp_rw [norm_smul, (shift _).norm_map]
      exact integral_mul_const ‖f‖ _

def convolution : ScalarL2 →L[ℂ] ScalarL2 :=
  (convolutionLinear k hk).mkContinuous (∫ y : Space, ‖k y‖) (convolutionLinear_norm_le k hk)

theorem convolution_apply (f : ScalarL2) : convolution k hk f = ∫ y : Space, k y • shift y f := rfl

theorem convolution_norm_le : ‖convolution k hk‖ ≤ ∫ y : Space, ‖k y‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _) (convolutionLinear_norm_le k hk)

/-- A cross-region convolution sees only kernel translations large
enough to connect the two regions. -/
theorem convolution_compressed_norm_le_tail (P Q : ScalarL2 →L[ℂ] ScalarL2)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (r : ℝ)
    (hvanish : ∀ y : Space, ‖y‖ < r → ∀ f : ScalarL2, P (shift y (Q f)) = 0) :
    ‖P * convolution k hk * Q‖ ≤ ∫ y : Space in {y | r ≤ ‖y‖}, ‖k y‖ := by
  have hset : MeasurableSet {y : Space | r ≤ ‖y‖} := isClosed_le continuous_const continuous_norm |>.measurableSet
  have ht : Integrable ({y : Space | r ≤ ‖y‖}.indicator (fun y => ‖k y‖)) := hk.norm.indicator hset
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _)
  intro f
  have he : (P * convolution k hk * Q) f = ∫ y : Space, k y • P (shift y (Q f)) := by
    change P (convolution k hk (Q f)) = _
    rw [convolution_apply, ← P.integral_comp_comm (convolution_integrable k hk (Q f))]
    simp only [map_smul]
  rw [he]
  have hb : ∀ y : Space, ‖k y • P (shift y (Q f))‖ ≤
      {y : Space | r ≤ ‖y‖}.indicator (fun y => ‖k y‖) y * ‖f‖ := by
    intro y
    by_cases hy : r ≤ ‖y‖
    · rw [Set.indicator_of_mem (show y ∈ {y : Space | r ≤ ‖y‖} from hy), norm_smul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ 1 * ‖shift y (Q f)‖ := P.le_of_opNorm_le hP _
        _ = ‖Q f‖ := by rw [one_mul, (shift y).norm_map]
        _ ≤ ‖f‖ := by simpa only [one_mul] using Q.le_of_opNorm_le hQ f
    · rw [hvanish y (lt_of_not_ge hy) f, smul_zero, norm_zero,
        Set.indicator_of_notMem (show y ∉ {y : Space | r ≤ ‖y‖} from hy), zero_mul]
  have hn := norm_integral_le_of_norm_le (ht.mul_const ‖f‖) (Filter.Eventually.of_forall hb)
  rw [integral_mul_const, integral_indicator hset] at hn
  exact hn

#print axioms convolution_norm_le
#print axioms convolution_compressed_norm_le_tail

end Maxwell.Continuum.KernelIntegral
