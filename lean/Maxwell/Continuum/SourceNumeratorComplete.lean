import Maxwell.Continuum.SourceNumeratorTheorem
import Maxwell.Continuum.SourceNumeratorDerivatives
import Maxwell.Continuum.MasterConstantLedger

/-! The positive analytic numerator of the actual continuum source,
including a uniform bound for every derivative order used in the
interaction calculation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Maxwell.Continuum.EffectiveMass

open Auxiliary FreeFiber PeriodicBand

attribute [local irreducible] realMode sourceFactor scaledSourceProduct

theorem positive_real_product {a b : ℂ} {t : ℝ}
    (ha : star a = a) (hb : star b = b)
    (hla : 1 / (2 : ℝ)^48 ≤ t * a.re)
    (hlb : 1 / (2 : ℝ)^48 ≤ t * b.re) :
    star (((t : ℂ)*a)*((t : ℂ)*b)) = ((t : ℂ)*a)*((t : ℂ)*b) ∧
    1 / (2 : ℝ)^96 ≤ (((t : ℂ)*a)*((t : ℂ)*b)).re := by
  have hai : a.im = 0 := Complex.conj_eq_iff_im.mp ha
  have hbi : b.im = 0 := Complex.conj_eq_iff_im.mp hb
  constructor
  · apply Complex.conj_eq_iff_im.mpr
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, hai, hbi,
      mul_zero, zero_mul, add_zero]
  · have hp := mul_le_mul hla hlb (by positivity)
      ((by positivity : (0 : ℝ) ≤ 1/2^48).trans hla)
    norm_num only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, hai, hbi, mul_zero, zero_mul, add_zero, sub_zero] at ⊢
    convert hp using 1
    norm_num

theorem physicalMomentum_real_smul (h : ℝ) (b : Space) :
    physicalMomentum (h • b) = (h : ℂ) • physicalMomentum b := by
  funext j
  change ((h * b j : ℝ) : ℂ) = (h : ℂ) * (b j : ℂ)
  exact Complex.ofReal_mul _ _

theorem scaled_imaginaryMomentum (h : ℝ) (b : Space) :
    (h : ℂ) • (Complex.I • physicalMomentum b) =
      Complex.I • physicalMomentum (h • b) := by
  rw [physicalMomentum_real_smul, smul_comm]

theorem scaledSourceProduct_imaginary_positive {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) {b : Space} (hb : ‖b‖ ≤ 1) :
    let N := scaledSourceProduct h (realMode D hh) (Complex.I • physicalMomentum b)
    star N = N ∧ 1 / (2 : ℝ)^96 ≤ N.re := by
  have hβ : ‖h • b‖ ≤ h := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos D.h_pos]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb D.h_pos.le
  have hnβ : ‖-(h • b)‖ ≤ h := by simpa only [norm_neg] using hβ
  have hm := sourceFactor_realMode_real D hh hβ
  have hp := sourceFactor_realMode_real D hh hnβ
  have hlm := sourceFactor_realMode_lower D hh hβ
  have hlp := sourceFactor_realMode_lower D hh hnβ
  rw [scaledSourceProduct, scaledSourceFactor, scaledSourceFactor,
    smul_neg, scaled_imaginaryMomentum, imaginaryMomentum_neg]
  exact positive_real_product hm hp hlm hlp

theorem source_derivative_ledger {n : ℕ} (hn : n ≤ 32) :
    (n.factorial : ℝ) * (2 : ℝ)^(4*n+64) ≤ (2 : ℝ)^352 := by
  have hf : (n.factorial : ℝ) ≤ (2 : ℝ)^160 := by
    apply le_trans _ MasterConstants.factorial32_le_power
    exact_mod_cast Nat.factorial_le hn
  calc
    _ ≤ (2 : ℝ)^160 * (2 : ℝ)^192 := by
      apply mul_le_mul hf (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity) (by positivity)
    _ = _ := by rw [← pow_add]

theorem actualSourceProduct_derivative_le {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) {k v : Momentum}
    (hk : ‖(h : ℂ) • k‖ ≤ analyticRadius / 2) (hi : ‖sourceImaginary k‖ ≤ 8)
    (hv : ‖v‖ ≤ 1) {n : ℕ} (hn : n ≤ 32) :
    ‖iteratedDeriv n (fun w : ℂ => scaledSourceProduct h (realMode D hh) (k + w • v)) 0‖ ≤
      (2 : ℝ)^352 := by
  have hhR : h ≤ analyticRadius :=
    hh.trans (by norm_num [analyticRadius, backgroundAmplitude])
  exact (scaledSourceProduct_iteratedDeriv_le D.h_pos hhR
    (realMode_norm D hh).le hk hi hv n).trans (source_derivative_ledger hn)

theorem actualSourceProduct_derivative_master {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) {k v : Momentum}
    (hk : ‖(h : ℂ) • k‖ ≤ analyticRadius / 2) (hi : ‖sourceImaginary k‖ ≤ 8)
    (hv : ‖v‖ ≤ 1) {n : ℕ} (hn : n ≤ 32) :
    ‖iteratedDeriv n (fun w : ℂ => scaledSourceProduct h (realMode D hh) (k + w • v)) 0‖ ≤
      MasterConstants.Cs :=
  (actualSourceProduct_derivative_le D hh hk hi hv hn).trans
    (MasterConstants.fixed_power_le_Cs (by have := MasterConstants.exponent_large; omega))

#print axioms scaledSourceProduct_imaginary_positive
#print axioms actualSourceProduct_derivative_master

end Maxwell.Continuum.EffectiveMass
