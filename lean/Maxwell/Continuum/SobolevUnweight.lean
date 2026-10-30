import Maxwell.Continuum.SobolevWeight
import Maxwell.Continuum.PEC

/-! Bounded inverse Bessel multipliers turn ordinary Schwartz density
in L² into simultaneous density for a field and its weak derivatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FourierSobolev

open MeasureTheory FourierTransform
open scoped SchwartzMap

def unweightData : FiberMultiplier.Data (H := ℂ) (volume : Measure Space) 1 where
  operator ξ := ((sobolevWeight ξ)⁻¹ : ℂ) • ContinuousLinearMap.id ℂ ℂ
  measurable := ((Complex.continuous_ofReal.comp sobolevWeight_continuous).inv₀
    fun ξ => Complex.ofReal_ne_zero.mpr (sobolevWeight_pos ξ).ne').aestronglyMeasurable.smul_const _
  nonneg := zero_le_one
  bound ξ := by
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (sobolevWeight_pos ξ)]
    exact (inv_le_one₀ (sobolevWeight_pos ξ)).mpr (sobolevWeight_one_le ξ)

def unweight : ScalarL2 →L[ℂ] ScalarL2 := unweightData.multiplier

theorem unweight_ae (F : ScalarL2) :
    unweight F =ᵐ[volume] fun ξ => ((sobolevWeight ξ)⁻¹ : ℂ)*F ξ :=
  unweightData.multiplier_ae F

theorem derivativeUnweight_norm (j : Fin 3) (ξ : Space) :
    ‖derivativeFactor j ξ*((sobolevWeight ξ)⁻¹ : ℂ)‖ ≤ 2*Real.pi := by
  rw [norm_mul, derivativeFactor_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sobolevWeight_pos ξ)]
  have hx0 : |ξ j| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ j
  have hx : |ξ j| ≤ sobolevWeight ξ := hx0.trans (sobolevWeight_norm_le ξ)
  have hw := (sobolevWeight_pos ξ).le
  calc
    _ ≤ (2*Real.pi*sobolevWeight ξ)*(sobolevWeight ξ)⁻¹ := by gcongr
    _ = _ := by rw [mul_assoc, mul_inv_cancel₀ (sobolevWeight_pos ξ).ne', mul_one]

def derivativeUnweightData (j : Fin 3) :
    FiberMultiplier.Data (H := ℂ) (volume : Measure Space) (2*Real.pi) where
  operator ξ := (derivativeFactor j ξ*((sobolevWeight ξ)⁻¹ : ℂ)) • ContinuousLinearMap.id ℂ ℂ
  measurable := ((derivativeFactor_continuous j).mul
    ((Complex.continuous_ofReal.comp sobolevWeight_continuous).inv₀
      fun ξ => Complex.ofReal_ne_zero.mpr (sobolevWeight_pos ξ).ne')).aestronglyMeasurable.smul_const _
  nonneg := mul_nonneg (by norm_num) Real.pi_pos.le
  bound ξ := by
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one]
    exact derivativeUnweight_norm j ξ

def derivativeUnweight (j : Fin 3) : ScalarL2 →L[ℂ] ScalarL2 := (derivativeUnweightData j).multiplier

theorem derivativeUnweight_ae (j : Fin 3) (F : ScalarL2) :
    derivativeUnweight j F =ᵐ[volume] fun ξ =>
      (derivativeFactor j ξ*((sobolevWeight ξ)⁻¹ : ℂ))*F ξ :=
  (derivativeUnweightData j).multiplier_ae F

theorem unweight_weighted (F : ScalarL2)
    (hF : ∀ j, MemLp (fun ξ => derivativeFactor j ξ*F ξ) 2 volume) :
    unweight (weightedL2 F hF) = F := by
  apply Lp.ext
  filter_upwards [unweight_ae (weightedL2 F hF), weightedL2_ae F hF] with ξ hu hw
  rw [hu, hw, inv_mul_cancel_left₀
    (Complex.ofReal_ne_zero.mpr (sobolevWeight_pos ξ).ne')]

theorem derivativeUnweight_weighted (F : ScalarL2)
    (hF : ∀ j, MemLp (fun ξ => derivativeFactor j ξ*F ξ) 2 volume) (j : Fin 3) :
    derivativeUnweight j (weightedL2 F hF) =ᵐ[volume] fun ξ => derivativeFactor j ξ*F ξ := by
  filter_upwards [derivativeUnweight_ae j (weightedL2 F hF), weightedL2_ae F hF] with ξ hu hw
  rw [hu, hw, mul_assoc, inv_mul_cancel_left₀
    (Complex.ofReal_ne_zero.mpr (sobolevWeight_pos ξ).ne')]

def unweightSchwartz (φ : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun ξ : Space => ((sobolevWeight ξ)⁻¹ : ℂ)) φ

theorem unweightSchwartz_apply (φ : SchwartzMap Space ℂ) (ξ : Space) :
    unweightSchwartz φ ξ = ((sobolevWeight ξ)⁻¹ : ℂ)*φ ξ :=
  SchwartzMap.smulLeftCLM_apply_apply inverseSobolevWeight_temperate φ ξ

theorem unweightSchwartz_toLp (φ : SchwartzMap Space ℂ) :
    (unweightSchwartz φ).toLp 2 volume = unweight (φ.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(unweightSchwartz φ).coeFn_toLp 2 volume, unweight_ae (φ.toLp 2 volume),
    φ.coeFn_toLp 2 volume] with ξ hl hr hφ
  rw [hl, hr, hφ, unweightSchwartz_apply]

theorem derivativeUnweightSchwartz_toLp (φ : SchwartzMap Space ℂ) (j : Fin 3) :
    (SchwartzMap.smulLeftCLM ℂ (derivativeFactor j) (unweightSchwartz φ)).toLp 2 volume =
      derivativeUnweight j (φ.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(SchwartzMap.smulLeftCLM ℂ (derivativeFactor j) (unweightSchwartz φ)).coeFn_toLp 2 volume,
    derivativeUnweight_ae j (φ.toLp 2 volume), φ.coeFn_toLp 2 volume] with ξ hl hr hφ
  rw [hl, hr, hφ, SchwartzMap.smulLeftCLM_apply_apply (derivativeFactor_temperate j), unweightSchwartz_apply]
  simp only [smul_eq_mul, mul_assoc]

#print axioms unweight_weighted
#print axioms derivativeUnweightSchwartz_toLp

end Maxwell.Continuum.FourierSobolev
