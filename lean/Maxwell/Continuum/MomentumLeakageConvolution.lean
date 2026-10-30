import Maxwell.Continuum.MomentumLeakageFourier
import Maxwell.Continuum.L1Convolution
import Maxwell.Continuum.WellMultiplier

/-! The high/low Fourier cross estimate with the actual reciprocal-torus
support sets. The remaining multiplier application supplies its literal
Fourier kernel; the cross estimate retains infinitely many aliases. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open Bloch MeasureTheory KernelIntegral

def frequencyHighProfile (s : ℝ) : Well.UnitProfile where
  coefficient := {ξ : Space | s ≤ quasiRadius ξ}.indicator (fun _ => 1)
  measurable := measurable_const.indicator (measurableSet_le measurable_const quasiRadius_measurable)
  nonneg ξ := by simp only [Set.indicator_apply]; split_ifs <;> norm_num
  le_one ξ := by simp only [Set.indicator_apply]; split_ifs <;> norm_num

def frequencyHigh (s : ℝ) : ScalarL2 →L[ℂ] ScalarL2 := (frequencyHighProfile s).multiplier

def frequencyLow (s : ℝ) : ScalarL2 →L[ℂ] ScalarL2 := 1-frequencyHigh s

theorem frequencyHigh_ae (s : ℝ) (f : ScalarL2) : frequencyHigh s f =ᵐ[volume]
    fun ξ => if s ≤ quasiRadius ξ then f ξ else 0 := by
  filter_upwards [(frequencyHighProfile s).multiplier_ae f] with ξ hξ
  change frequencyHigh s f ξ = _ at hξ
  rw [hξ]
  simp only [frequencyHighProfile, Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp

theorem frequencyLow_ae (s : ℝ) (f : ScalarL2) : frequencyLow s f =ᵐ[volume]
    fun ξ => if s ≤ quasiRadius ξ then 0 else f ξ := by
  filter_upwards [Lp.coeFn_sub f (frequencyHigh s f), frequencyHigh_ae s f] with ξ hs hp
  change (f-frequencyHigh s f : ScalarL2) ξ = _
  rw [hs, Pi.sub_apply, hp]
  split_ifs <;> simp

theorem frequencyHigh_norm_le (s : ℝ) : ‖frequencyHigh s‖ ≤ 1 :=
  (frequencyHighProfile s).multiplier_norm_le

theorem frequencyLow_norm_le (s : ℝ) : ‖frequencyLow s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [frequencyLow_ae s f] with ξ hξ
  rw [hξ]
  split_ifs <;> simp

theorem frequencyHigh_fieldFourier (s : ℝ) (f : FieldL2) (j : Fin 3) :
    frequencyHigh s (fieldFourier f j) = fieldFourier (highMomentumProjection s f) j := by
  apply Lp.ext
  exact (frequencyHigh_ae s _).trans (highMomentumProjection_fourier_ae s f j).symm

theorem frequencyLow_fieldFourier (s : ℝ) (f : FieldL2) (j : Fin 3) :
    frequencyLow s (fieldFourier f j) = fieldFourier (f-highMomentumProjection s f) j := by
  apply Lp.ext
  exact (frequencyLow_ae s _).trans (lowMomentumProjection_fourier_ae s f j).symm

theorem frequencyHigh_shift_low_zero (s r : ℝ) (y : Space)
    (hy : ‖y‖ < (s-r)/(2*Real.pi)) (f : ScalarL2) :
    frequencyHigh s (shift y (frequencyLow r f)) = 0 := by
  have hshift := (measurePreserving_add_right volume (-y)).quasiMeasurePreserving.ae_eq_comp
    (frequencyLow_ae r f)
  apply Lp.ext
  filter_upwards [frequencyHigh_ae s (shift y (frequencyLow r f)),
    shift_ae y (frequencyLow r f), hshift, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure Space))]
    with ξ hp hs hl hzero
  rw [hp, hzero]
  simp only [Pi.zero_apply]
  by_cases hξ : s ≤ quasiRadius ξ
  · simp only [hξ, ↓reduceIte]
    rw [hs]
    have hr : r ≤ quasiRadius (ξ-y) := by
      by_contra hnot
      have hd := physicalFrequency_separation (s := s) (Δ := s-r) hξ
        (show quasiRadius (ξ-y) ≤ s-(s-r) by linarith [lt_of_not_ge hnot])
      rw [sub_sub_cancel] at hd
      have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2*Real.pi)).mp hy
      nlinarith
    have he : ξ + -y = ξ-y := by abel
    dsimp only [Function.comp_apply] at hl
    rw [he] at hl
    simpa only [hr, ↓reduceIte] using hl
  · simp [hξ]

theorem frequency_cross_convolution_norm (k : Space → ℂ) (hk : Integrable k) (s r : ℝ) :
    ‖frequencyHigh s * KernelIntegral.convolution k hk * frequencyLow r‖ ≤
      ∫ y : Space in {y | (s-r)/(2*Real.pi) ≤ ‖y‖}, ‖k y‖ :=
  convolution_compressed_norm_le_tail k hk (frequencyHigh s) (frequencyLow r)
    (frequencyHigh_norm_le s) (frequencyLow_norm_le r) _ (frequencyHigh_shift_low_zero s r)

#print axioms frequencyHigh_fieldFourier
#print axioms frequency_cross_convolution_norm

end Maxwell.Continuum.Auxiliary
