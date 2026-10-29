import Maxwell.Continuum.PeriodicPoleScaled
import Maxwell.Continuum.SourceNumeratorComplete

/-! The actual analytic source numerator at the constructed imaginary
pole, including its positive quantitative lower bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary

attribute [local irreducible] imaginaryPole EffectiveMass.realMode
  EffectiveMass.scaledSourceProduct EffectiveMass.sourceFactor

def scaledPoleVector {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : Space :=
  PiLp.single 2 j (imaginaryPole D hh j / h)

theorem scaledPoleVector_norm {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    ‖scaledPoleVector D hh j‖ = imaginaryPole D hh j / h := by
  simp only [scaledPoleVector, PiLp.norm_single, Real.norm_eq_abs,
    abs_of_pos (div_pos (imaginaryPole_pos D hh j) D.h_pos)]

theorem scaledPoleVector_norm_le {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : ‖scaledPoleVector D hh j‖ ≤ 1 := by
  rw [scaledPoleVector_norm]
  exact imaginaryPole_scaled_le_one D hh j

theorem scaledPoleVector_physical {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    EffectiveMass.physicalMomentum (scaledPoleVector D hh j) =
      ((imaginaryPole D hh j / h : ℝ) : ℂ) • basisVector j := by
  funext k
  simp only [EffectiveMass.physicalMomentum, realMomentum, scaledPoleVector,
    PiLp.single_apply, basisVector_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp_all

theorem actualSourceProduct_at_pole {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    let N := EffectiveMass.scaledSourceProduct h (EffectiveMass.realMode D hh)
      ((((imaginaryPole D hh j / h : ℝ) : ℂ) * Complex.I) • basisVector j)
    star N = N ∧ 1 / (2 : ℝ)^96 ≤ N.re := by
  have hp := EffectiveMass.scaledSourceProduct_imaginary_positive D hh
    (scaledPoleVector_norm_le D hh j)
  rw [scaledPoleVector_physical, smul_smul, mul_comm Complex.I] at hp
  exact hp

end Maxwell.Continuum.PeriodicBand
