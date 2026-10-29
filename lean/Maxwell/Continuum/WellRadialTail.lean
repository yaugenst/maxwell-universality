import Maxwell.Continuum.WellFourierDeriv
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Gamma

/-! An explicit integrable radial majorant for the Gevrey Fourier tail. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Set Metric

def tailMajorant (p : Space) : ℝ := Real.exp (-Real.sqrt ‖p‖ / 512)

theorem tailMajorant_integrable : Integrable tailMajorant (volume : Measure Space) := by
  unfold tailMajorant
  apply (integrable_fun_norm_addHaar (volume : Measure Space)
    (f := fun r : ℝ => Real.exp (-Real.sqrt r / 512))).mpr
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 / 2 : ℝ))
    (s := (2 : ℝ)) (b := (1 / 512 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ext r
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
    smul_eq_mul, Real.rpow_two, Real.sqrt_eq_rpow]
  congr 1
  congr 1
  ring

theorem tailMajorant_radial_integral :
    (∫ r : ℝ in Ioi 0, r ^ 2 * Real.exp (-Real.sqrt r / 512)) =
      240 * (512 : ℝ) ^ 6 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (1 / 2 : ℝ))
    (q := (2 : ℝ)) (b := (1 / 512 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hG : Real.Gamma (6 : ℝ) = 120 := by
    norm_num
  have he : (fun r : ℝ => r ^ (2 : ℝ) * Real.exp (-(1 / 512 : ℝ) * r ^ (1 / 2 : ℝ))) =
      (fun r : ℝ => r ^ 2 * Real.exp (-Real.sqrt r / 512)) := by
    funext r
    rw [Real.rpow_two, Real.sqrt_eq_rpow]
    congr 1
    congr 1
    ring
  rw [he] at h
  norm_num [Real.rpow_neg, Real.rpow_natCast, hG] at h ⊢
  exact h

theorem tailMajorant_integral_le : (∫ p, tailMajorant p) ≤ (2 : ℝ) ^ 80 := by
  have he := integral_fun_norm_addHaar (volume : Measure Space)
    (fun r : ℝ => Real.exp (-Real.sqrt r / 512))
  have hv : (volume : Measure Space).real (ball 0 1) ≤ 8 := by
    rw [measureReal_def, EuclideanSpace.volume_ball_fin_three]
    norm_num only [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal
      (by positivity : 0 ≤ Real.pi * 4 / 3)]
    linarith [Real.pi_lt_four]
  have he' : (∫ p, tailMajorant p) =
      3 * (volume : Measure Space).real (ball 0 1) * (240 * (512 : ℝ) ^ 6) := by
    simpa only [tailMajorant, Space, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
      nsmul_eq_mul, smul_eq_mul, tailMajorant_radial_integral, Nat.cast_ofNat, mul_assoc] using he
  rw [he']
  calc
    3 * (volume : Measure Space).real (ball 0 1) * (240 * (512 : ℝ) ^ 6) ≤
        3 * 8 * (240 * (512 : ℝ) ^ 6) := by gcongr
    _ ≤ (2 : ℝ) ^ 80 := by norm_num

/-- Splitting the exponential leaves an integrable majorant and the required tail exponent. -/
theorem sqrt_decay_tail (F : Space → ℝ) (hF : ∀ p, 0 ≤ F p)
    (hb : ∀ p, F p ≤ (2 : ℝ) ^ 20 * Real.exp (-Real.sqrt ‖p‖ / 256)) (R : ℝ) :
    (∫ p in {p : Space | R ≤ ‖p‖}, F p) ≤
      (2 : ℝ) ^ 100 * Real.exp (-Real.sqrt R / 512) := by
  have hcoef : 0 ≤ (2 : ℝ) ^ 20 * Real.exp (-Real.sqrt R / 512) := by positivity
  have hi := tailMajorant_integrable.const_mul ((2 : ℝ) ^ 20 * Real.exp (-Real.sqrt R / 512))
  have hbound : ∀ᵐ p ∂volume.restrict {p : Space | R ≤ ‖p‖},
      F p ≤ ((2 : ℝ) ^ 20 * Real.exp (-Real.sqrt R / 512)) * tailMajorant p := by
    filter_upwards [ae_restrict_mem (by measurability : MeasurableSet {p : Space | R ≤ ‖p‖})] with p hp
    apply (hb p).trans
    rw [tailMajorant, mul_assoc, ← Real.exp_add]
    gcongr
    have hs := Real.sqrt_le_sqrt hp
    linarith
  calc
    (∫ p in {p : Space | R ≤ ‖p‖}, F p) ≤
        ∫ p in {p : Space | R ≤ ‖p‖},
          ((2 : ℝ) ^ 20 * Real.exp (-Real.sqrt R / 512)) * tailMajorant p :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall hF) hi.integrableOn hbound
    _ ≤ ∫ p, ((2 : ℝ) ^ 20 * Real.exp (-Real.sqrt R / 512)) * tailMajorant p :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall (fun p => mul_nonneg hcoef (Real.exp_pos _).le))
    _ = ((2 : ℝ) ^ 20 * Real.exp (-Real.sqrt R / 512)) * (∫ p, tailMajorant p) :=
      integral_const_mul _ _
    _ ≤ ((2 : ℝ) ^ 20 * Real.exp (-Real.sqrt R / 512)) * (2 : ℝ) ^ 80 :=
      mul_le_mul_of_nonneg_left tailMajorant_integral_le hcoef
    _ = (2 : ℝ) ^ 100 * Real.exp (-Real.sqrt R / 512) := by ring

end Maxwell.Continuum.Well
