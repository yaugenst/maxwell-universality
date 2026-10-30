import Maxwell.Continuum.MomentumLeakageWellTail
import Maxwell.Continuum.MomentumLeakageConvolution

/-! The manuscript Fourier-cross estimate for the literal finite
assembled physical potential, on all vector polarizations and aliases. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open MeasureTheory FourierTransform Bloch

attribute [local irreducible] Bloch.unitary highMomentumProjection

def lowMomentumProjection (s : ℝ) : FieldL2 →L[ℂ] FieldL2 := 1-highMomentumProjection s

theorem translatedWell_cross_fourier {h : ℝ} (hh : 0 < h) (x : Space)
    (s r : ℝ) (f : FieldL2) (j : Fin 3) :
    fieldFourier ((highMomentumProjection s * translatedWell h x * lowMomentumProjection r) f) j =
      (frequencyHigh s * KernelIntegral.convolution (translatedWellKernel h x)
        (translatedWellKernel_integrable hh x) * frequencyLow r) (fieldFourier f j) := by
  change fieldFourier (highMomentumProjection s (translatedWell h x (lowMomentumProjection r f))) j = _
  rw [← frequencyHigh_fieldFourier]
  change frequencyHigh s (𝓕 ((translatedWellProfile h x).multiplier (lowMomentumProjection r f j))) = _
  rw [← translatedWell_fourier_convolution hh x]
  change frequencyHigh s (KernelIntegral.convolution _ _
    (fieldFourier (f-highMomentumProjection r f) j)) = _
  rw [← frequencyLow_fieldFourier]
  rfl

theorem translatedWell_cross_norm {h : ℝ} (hh : 0 < h) (x : Space) (s r : ℝ) :
    ‖highMomentumProjection s * translatedWell h x * lowMomentumProjection r‖ ≤
      (2 : ℝ)^100 * Real.exp (-Real.sqrt ((s-r)/h)/512) := by
  let C : ℝ := (2 : ℝ)^100 * Real.exp (-Real.sqrt ((s-r)/h)/512)
  have hC : 0 ≤ C := by positivity
  have hb : ‖frequencyHigh s * KernelIntegral.convolution (translatedWellKernel h x)
      (translatedWellKernel_integrable hh x) * frequencyLow r‖ ≤ C :=
    (frequency_cross_convolution_norm _ _ s r).trans (translatedWellKernel_tail hh x (s-r))
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  rw [← fieldFourier.norm_map f, ← fieldFourier.norm_map
    ((highMomentumProjection s * translatedWell h x * lowMomentumProjection r) f)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [translatedWell_cross_fourier hh x s r f j, ← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr
    (ContinuousLinearMap.le_of_opNorm_le _ hb _)

variable {ι : Type*} [Fintype ι]

theorem finiteWell_cross_norm_sum {h : ℝ} (hh : 0 < h) (x : ι → Space) (v : ι → ℝ)
    (s r : ℝ) :
    ‖highMomentumProjection s * finiteWellOperator h x v * lowMomentumProjection r‖ ≤
      (∑ i, |v i|) * ((2 : ℝ)^100 * Real.exp (-Real.sqrt ((s-r)/h)/512)) := by
  classical
  have he : highMomentumProjection s * finiteWellOperator h x v * lowMomentumProjection r =
      ∑ i, (v i : ℂ) • (highMomentumProjection s * translatedWell h (x i) * lowMomentumProjection r) := by
    simp only [finiteWellOperator, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply ContinuousLinearMap.ext
    intro f
    change highMomentumProjection s ((v i : ℂ) • translatedWell h (x i) (lowMomentumProjection r f)) = _
    rw [map_smul]
    rfl
  rw [he, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (translatedWell_cross_norm hh (x i) s r) (abs_nonneg _)

theorem finiteWell_cross_norm {h V : ℝ} (hh : 0 < h) (x : ι → Space) (v : ι → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ V) (s r : ℝ) :
    ‖highMomentumProjection s * finiteWellOperator h x v * lowMomentumProjection r‖ ≤
      (2 : ℝ)^100 * (Fintype.card ι : ℝ) * V * Real.exp (-Real.sqrt ((s-r)/h)/512) := by
  apply (finiteWell_cross_norm_sum hh x v s r).trans
  have hs : (∑ i, |v i|) ≤ (Fintype.card ι : ℝ)*V := by
    calc
      _ ≤ ∑ _i : ι, V := Finset.sum_le_sum fun i _ => by rw [abs_of_nonneg (hv0 i)]; exact hv i
      _ = _ := by simp
  calc
    _ ≤ ((Fintype.card ι : ℝ)*V) * ((2 : ℝ)^100 * Real.exp (-Real.sqrt ((s-r)/h)/512)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by ring

#print axioms translatedWell_cross_norm
#print axioms finiteWell_cross_norm

end Maxwell.Continuum.Auxiliary
