import Maxwell.Continuum.EffectiveMassSourceMode
import Maxwell.Continuum.EffectiveMassPacketWave
import Maxwell.Continuum.FiniteSupportKernel
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! The literal compact source as a vector-valued integrable function.
The L¹ estimate uses its actual vector L² norm, without a component-count loss. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber Set Metric

theorem fieldValue_memLp (u : FieldL2) : MemLp (fieldValue u) 2 (volume : Measure Space) :=
  memLp_piLp_iff.mpr (fun j => Lp.memLp (u j))

def fieldVectorL2 (u : FieldL2) : Lp Polarization 2 (volume : Measure Space) :=
  (fieldValue_memLp u).toLp (fieldValue u)

theorem fieldVectorL2_ae (u : FieldL2) : fieldVectorL2 u =ᵐ[volume] fieldValue u :=
  MemLp.coeFn_toLp _

theorem fieldVectorL2_norm (u : FieldL2) : ‖fieldVectorL2 u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    L2.inner_def, field_inner_eq_integral]
  congr 1
  exact integral_congr_ae ((fieldVectorL2_ae u).mono fun x hx =>
    congrArg (fun v : Polarization => inner ℂ v v) hx)

theorem fieldValue_integrableOn (u : FieldL2) (r : ℝ) :
    IntegrableOn (fieldValue u) (closedBall 0 r) := by
  apply integrable_piLp_iff.mpr
  intro j
  exact integrableOn_Lp_of_measure_ne_top (u j) (by norm_num)
    (isCompact_closedBall (0 : Space) r).measure_ne_top

theorem fieldValue_setIntegral_norm_le (u : FieldL2) (r : ℝ) :
    ∫ x in closedBall (0 : Space) r, ‖fieldValue u x‖ ≤
      Real.sqrt (volume.real (closedBall (0 : Space) r)) * ‖u‖ := by
  let g : Lp ℝ 2 (volume : Measure Space) :=
    (fieldValue_memLp u).norm.toLp (fun x => ‖fieldValue u x‖)
  have hg : g =ᵐ[volume] fun x => ‖fieldValue u x‖ := MemLp.coeFn_toLp _
  have hgn : ‖g‖ = ‖u‖ := by
    rw [← fieldVectorL2_norm u, fieldVectorL2, Lp.norm_toLp, Lp.norm_toLp,
      eLpNorm_norm _ (fieldValue_memLp u).aestronglyMeasurable]
  have hi := L2.inner_indicatorConstLp_one measurableSet_closedBall
    (isCompact_closedBall (0 : Space) r).measure_ne_top g
  have hid : inner ℝ (indicatorConstLp 2 measurableSet_closedBall
      (isCompact_closedBall (0 : Space) r).measure_ne_top 1) g =
      ∫ x in closedBall (0 : Space) r, ‖fieldValue u x‖ := by
    rw [hi]
    exact integral_congr_ae (ae_restrict_of_ae hg)
  rw [← hid]
  calc
    _ ≤ ‖inner ℝ (indicatorConstLp 2 measurableSet_closedBall
        (isCompact_closedBall (0 : Space) r).measure_ne_top 1) g‖ := le_abs_self _
    _ ≤ ‖indicatorConstLp (E := ℝ) 2 measurableSet_closedBall
        (isCompact_closedBall (0 : Space) r).measure_ne_top 1‖ * ‖g‖ :=
      norm_inner_le_norm _ _
    _ = _ := by rw [KernelIntegral.indicator_one_norm, hgn]

def sourceValue (h : ℝ) (u : FieldL2) : Space → Polarization :=
  fieldValue (sourceMode h u)

theorem sourceValue_supported {h : ℝ} (hh : 0 < h) (u : FieldL2) :
    ∀ᵐ x ∂(volume : Measure Space), h⁻¹ ≤ ‖x‖ → sourceValue h u x = 0 := by
  filter_upwards [ae_all_iff.mpr (fun j => sourceMode_supported hh u j)] with x hx hnorm
  apply PiLp.ext
  intro j
  exact hx j hnorm

theorem sourceValue_integrable {h : ℝ} (hh : 0 < h) (u : FieldL2) :
    Integrable (sourceValue h u) := by
  apply (fieldValue_integrableOn (sourceMode h u) h⁻¹).integrable_of_ae_notMem_eq_zero
  filter_upwards [sourceValue_supported hh u] with x hx hnot
  apply hx
  simp only [mem_closedBall, dist_zero_right, not_le] at hnot
  exact hnot.le

theorem sourceValue_integral_norm_le {h : ℝ} (hh : 0 < h) (u : FieldL2) :
    ∫ x, ‖sourceValue h u x‖ ≤ Real.sqrt (volume.real (closedBall (0 : Space) h⁻¹)) * ‖u‖ := by
  have heq : ∫ x in closedBall (0 : Space) h⁻¹, ‖sourceValue h u x‖ =
      ∫ x, ‖sourceValue h u x‖ := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [sourceValue_supported hh u] with x hx hnot
    simp only [mem_closedBall, dist_zero_right, not_le] at hnot
    rw [hx hnot.le, norm_zero]
  rw [← heq]
  exact (fieldValue_setIntegral_norm_le (sourceMode h u) h⁻¹).trans
    (mul_le_mul_of_nonneg_left (sourceMode_norm_le h u) (Real.sqrt_nonneg _))

def sourceScale (h : ℝ) : ℝ := h * Real.sqrt h

theorem sourceScale_pos {h : ℝ} (hh : 0 < h) : 0 < sourceScale h :=
  mul_pos hh (Real.sqrt_pos.mpr hh)

theorem sourceScale_sqrt_volume_le {h : ℝ} (hh : 0 < h) :
    sourceScale h * Real.sqrt (volume.real (closedBall (0 : Space) h⁻¹)) ≤ 3 := by
  have hv : volume.real (closedBall (0 : Space) h⁻¹) = Real.pi * 4 / 3 * (h⁻¹)^3 := by
    rw [measureReal_def, EuclideanSpace.volume_closedBall_fin_three,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
    ring
  have hs : (sourceScale h * Real.sqrt (volume.real (closedBall (0 : Space) h⁻¹)))^2 =
      Real.pi * 4 / 3 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hv, sourceScale, mul_pow, Real.sq_sqrt hh.le]
    field_simp
  have hn : 0 ≤ sourceScale h * Real.sqrt (volume.real (closedBall (0 : Space) h⁻¹)) :=
    mul_nonneg (sourceScale_pos hh).le (Real.sqrt_nonneg _)
  nlinarith [Real.pi_lt_four]

theorem sourceValue_scaled_integral_norm_le {h : ℝ} (hh : 0 < h) (u : FieldL2) :
    sourceScale h * ∫ x, ‖sourceValue h u x‖ ≤ 3 * ‖u‖ := by
  calc
    _ ≤ sourceScale h * (Real.sqrt (volume.real (closedBall (0 : Space) h⁻¹)) * ‖u‖) :=
      mul_le_mul_of_nonneg_left (sourceValue_integral_norm_le hh u) (sourceScale_pos hh).le
    _ = (sourceScale h * Real.sqrt (volume.real (closedBall (0 : Space) h⁻¹))) * ‖u‖ :=
      (mul_assoc _ _ _).symm
    _ ≤ 3 * ‖u‖ := mul_le_mul_of_nonneg_right (sourceScale_sqrt_volume_le hh) (norm_nonneg _)

#print axioms sourceValue_integrable
#print axioms sourceValue_scaled_integral_norm_le

end Maxwell.Continuum.EffectiveMass
