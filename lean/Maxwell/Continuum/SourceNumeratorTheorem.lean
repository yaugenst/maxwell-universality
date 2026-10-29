import Maxwell.Continuum.SourceNumeratorPositive

/-! Both signed analytic source factors satisfy the continuum paper's
real, positive imaginary-momentum lower bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open Auxiliary FreeFiber

def sourcePlus (h : ℝ) (u : FieldL2) (q : Momentum) : ℂ := sourceFactor h u (-q)

def sourceMinus (h : ℝ) (u : FieldL2) (q : Momentum) : ℂ := sourceFactor h u q

theorem sourceScale_eq_rpow {h : ℝ} (hh : 0 < h) : sourceScale h = h ^ (3 / 2 : ℝ) :=
  (sourceScale_eq_envelope_factor hh).trans (envelope_dilation_factor hh)

theorem imaginaryMomentum_neg (β : Space) :
    -(Complex.I • physicalMomentum β) = Complex.I • physicalMomentum (-β) := by
  funext j
  change -(Complex.I * (β j : ℂ)) = Complex.I * ((-β j : ℝ) : ℂ)
  simp

/-- The lower-bound and reality part of the analytic source-numerator lemma.
The field is the canonical real eigenmode of the literal continuum Sh. -/
theorem sourceNumerators_positive {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) {β : Space} (hβ : ‖β‖ ≤ h) :
    let q := Complex.I • physicalMomentum β
    let u := realMode D hh
    star (sourcePlus h u q) = sourcePlus h u q ∧
    star (sourceMinus h u q) = sourceMinus h u q ∧
    1 / (2 : ℝ)^48 ≤ h ^ (3 / 2 : ℝ) * (sourcePlus h u q).re ∧
    1 / (2 : ℝ)^48 ≤ h ^ (3 / 2 : ℝ) * (sourceMinus h u q).re := by
  dsimp only
  have hβneg : ‖-β‖ ≤ h := by simpa only [norm_neg] using hβ
  have hpReal := sourceFactor_realMode_real D hh hβneg
  have hpLower := sourceFactor_realMode_lower D hh hβneg
  have hmReal := sourceFactor_realMode_real D hh hβ
  have hmLower := sourceFactor_realMode_lower D hh hβ
  rw [sourceScale_eq_rpow D.h_pos] at hpLower hmLower
  simp only [sourcePlus, sourceMinus, imaginaryMomentum_neg]
  exact ⟨hpReal, hmReal, hpLower, hmLower⟩

end Maxwell.Continuum.EffectiveMass
