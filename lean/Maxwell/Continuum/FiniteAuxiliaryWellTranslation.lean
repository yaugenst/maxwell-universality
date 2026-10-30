import Maxwell.Continuum.FiniteAuxiliarySourceEquation
import Maxwell.Continuum.WellTranslation

/-! Translation stability of the actual finite potential, independent
of the number of disjoint wells. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass Bloch MeasureTheory

theorem well_difference (x y : Space) : |Well.w x-Well.w y| ≤ 800*‖x-y‖ := by
  have hq := Well.qw_lipschitz.norm_sub_le x y
  simp only [Real.norm_eq_abs, NNReal.coe_ofNat] at hq
  have hs : |Well.qw x+Well.qw y| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg (Well.qw_nonneg x) (Well.qw_nonneg y))]
    linarith only [Well.qw_le_one x, Well.qw_le_one y]
  calc
    |Well.w x-Well.w y| = |Well.qw x-Well.qw y| * |Well.qw x+Well.qw y| := by
      rw [← abs_mul, ← Well.qw_sq, ← Well.qw_sq]
      congr 1
      ring
    _ ≤ (400*‖x-y‖)*2 := mul_le_mul hq hs (abs_nonneg _) (by positivity)
    _ = _ := by ring

variable {ι : Type*} [Fintype ι]

theorem finiteWellCoefficient_single {h : ℝ} (hh : 0 < h) (r : ι → Space) (v : ι → ℝ)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (x : Space) (i : ι) (hi : Well.w (h • (x-r i)) ≠ 0) :
    finiteWellCoefficient h r v x = v i*Well.w (h • (x-r i)) := by
  classical
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hz : Well.w (h • (x-r j)) = 0 := by
      by_contra hj
      exact Set.disjoint_left.mp (hdisj hji)
        (translatedWell_nonzero_mem_ball hh (r j) x hj)
        (translatedWell_nonzero_mem_ball hh (r i) x hi)
    rw [hz, mul_zero]
  · simp

private theorem coefficient_sub_le {h V : ℝ} (hh : 0 < h) (hV : 0 ≤ V)
    (r : ι → Space) (v : ι → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ V)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (x y : Space) : finiteWellCoefficient h r v x-finiteWellCoefficient h r v y ≤ 800*V*h*‖x-y‖ := by
  classical
  by_cases he : ∃ i, Well.w (h • (x-r i)) ≠ 0
  · obtain ⟨i, hi⟩ := he
    have hy : v i*Well.w (h • (y-r i)) ≤ finiteWellCoefficient h r v y := by
      unfold finiteWellCoefficient
      exact Finset.single_le_sum (f := fun j => v j*Well.w (h • (y-r j)))
        (fun j _ => mul_nonneg (hv0 j) (Well.w_nonneg _)) (Finset.mem_univ i)
    have hw := well_difference (h • (x-r i)) (h • (y-r i))
    rw [← smul_sub, show (x-r i)-(y-r i) = x-y by abel, norm_smul,
      Real.norm_of_nonneg hh.le] at hw
    rw [finiteWellCoefficient_single hh r v hdisj x i hi]
    calc
      v i*Well.w (h • (x-r i))-finiteWellCoefficient h r v y
          ≤ v i*(Well.w (h • (x-r i))-Well.w (h • (y-r i))) := by nlinarith only [hy]
      _ ≤ v i*|Well.w (h • (x-r i))-Well.w (h • (y-r i))| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (hv0 i)
      _ ≤ V*(800*(h*‖x-y‖)) := mul_le_mul (hv i) hw (abs_nonneg _) hV
      _ = _ := by ring
  · have hz : finiteWellCoefficient h r v x = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [show Well.w (h • (x-r i)) = 0 from not_not.mp (fun hn => he ⟨i, hn⟩), mul_zero]
    rw [hz]
    have hy := (finiteWellCoefficient_bounds hh hV r v hv0 hv hdisj y).1
    exact (sub_nonpos.mpr hy).trans (by positivity)

theorem finiteWellCoefficient_difference {h V : ℝ} (hh : 0 < h) (hV : 0 ≤ V)
    (r : ι → Space) (v : ι → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ V)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (x y : Space) : |finiteWellCoefficient h r v x-finiteWellCoefficient h r v y| ≤ 800*V*h*‖x-y‖ := by
  apply abs_le.mpr
  constructor
  · have he := coefficient_sub_le hh hV r v hv0 hv hdisj y x
    rw [norm_sub_rev] at he
    linarith only [he]
  · exact coefficient_sub_le hh hV r v hv0 hv hdisj x y

def wellTranslationCommutator (h : ℝ) (r : ι → Space) (v : ι → ℝ) (a : Space) :
    FieldL2 →L[ℂ] FieldL2 :=
  translationOperator a*finiteWellOperator h r v-finiteWellOperator h r v*translationOperator a

theorem wellTranslationCommutator_ae (h : ℝ) (r : ι → Space) (v : ι → ℝ) (a : Space)
    (f : FieldL2) (j : Fin 3) :
    wellTranslationCommutator h r v a f j =ᵐ[volume] fun x =>
      ((finiteWellCoefficient h r v (x+a)-finiteWellCoefficient h r v x : ℝ) : ℂ)*f j (x+a) := by
  have hp := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp
    (finiteWellOperator_ae h r v f j)
  filter_upwards [fieldTranslation_ae a (finiteWellOperator h r v f) j,
    finiteWellOperator_ae h r v (fieldTranslation a f) j, fieldTranslation_ae a f j,
    Lp.coeFn_sub (fieldTranslation a (finiteWellOperator h r v f) j)
      (finiteWellOperator h r v (fieldTranslation a f) j), hp] with x ht hm hf hs hp
  change (fieldTranslation a (finiteWellOperator h r v f) j-
    finiteWellOperator h r v (fieldTranslation a f) j) x = _
  dsimp only [Function.comp_apply] at hp
  rw [hs]
  simp only [Pi.sub_apply]
  rw [ht, hp, hm, hf, Complex.ofReal_sub, sub_mul]

theorem wellTranslationCommutator_norm {h V : ℝ} (hh : 0 < h) (hV : 0 ≤ V)
    (r : ι → Space) (v : ι → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ V)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (a : Space) : ‖wellTranslationCommutator h r v a‖ ≤ 800*V*h*‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  have hb (j : Fin 3) : ‖wellTranslationCommutator h r v a f j‖ ≤ (800*V*h*‖a‖)*‖f j‖ := by
    rw [← (translation a).norm_map (f j)]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [wellTranslationCommutator_ae h r v a f j, translation_ae a (f j)] with x hc ht
    rw [hc, ht, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [add_sub_cancel_left] using finiteWellCoefficient_difference hh hV r v hv0 hv hdisj (x+a) x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hb j)

#print axioms finiteWellCoefficient_difference
#print axioms wellTranslationCommutator_norm

end Maxwell.Continuum.FiniteAuxiliary
