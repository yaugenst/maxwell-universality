import Maxwell.Continuum.CalibrationFiniteVector
import Maxwell.Continuum.RationalSquareRootEvaluation
import Maxwell.Continuum.CalibrationPowerNormalize

/-! Rational normalization of a finite Fourier vector, using its exact
finite squared norm and an executable integer-square-root enclosure. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber NormedSpace

def rationalNormCenter (f : RationalAliasField) (R P : ℕ) : ℚ :=
  sqrtRationalCenter (rationalNormSq f R) P

def rationalNormalize (f : RationalAliasField) (R P : ℕ) : RationalAliasField :=
  (rationalNormCenter f R P)⁻¹ • f

theorem rationalNormCenter_nonneg (f : RationalAliasField) (R P : ℕ) :
    0 ≤ rationalNormCenter f R P := sqrtRationalCenter_nonneg _ _

noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem rationalNormCenter_error {f : RationalAliasField} {u : FiberSpace} {R : ℕ}
    (hf : RationalSupported f R) (hu : Represents f u) (P : ℕ) :
    |(rationalNormCenter f R P : ℝ)-‖u‖| ≤ (1/2 : ℝ)^P := by
  have h := sqrtRational_error (rationalNormSq f R) (rationalNormSq_nonneg f R) P
  rw [rationalNormSq_eq hf hu,Real.sqrt_sq (norm_nonneg _)] at h
  exact h

theorem rationalNormalize_represents {f : RationalAliasField} {u : FiberSpace} {R : ℕ}
    (hu : Represents f u) (P : ℕ) :
    Represents (rationalNormalize f R P) (((rationalNormCenter f R P)⁻¹ : ℚ) • u) := by
  simpa only [Rat.cast_smul_eq_qsmul,rationalNormalize] using represents_smul ((rationalNormCenter f R P)⁻¹) hu

theorem rationalNormalize_error {f : RationalAliasField} {u : FiberSpace} {R : ℕ}
    (hf : RationalSupported f R) (hu : Represents f u) (P : ℕ)
    (hsmall : (1/2 : ℝ)^P ≤ ‖u‖/2) :
    0 < rationalNormCenter f R P ∧
      ‖(((rationalNormCenter f R P)⁻¹ : ℚ) • u)-normalize u‖ ≤ 2*(1/2 : ℝ)^P/‖u‖ := by
  have he := rationalNormCenter_error hf hu P
  have hε : (0 : ℝ) < (1/2 : ℝ)^P := by positivity
  have hu0 : 0 < ‖u‖ := by linarith
  have ha : ‖u‖/2 ≤ (rationalNormCenter f R P : ℝ) := by
    have h := (abs_le.mp he).1
    linarith
  have ha0 : (0 : ℝ) < rationalNormCenter f R P := by linarith
  refine ⟨by exact_mod_cast ha0,?_⟩
  have hcast : (((rationalNormCenter f R P)⁻¹ : ℚ) • u) =
      ((rationalNormCenter f R P : ℝ)⁻¹) • u := by
    rw [← Rat.cast_smul_eq_qsmul ℝ,Rat.cast_inv]
  rw [hcast]
  have hid : ((rationalNormCenter f R P : ℝ)⁻¹) • u-normalize u =
      ((rationalNormCenter f R P : ℝ)⁻¹-‖u‖⁻¹) • u := by
    rw [sub_smul]
    rfl
  rw [hid,norm_smul,Real.norm_eq_abs,inv_sub_inv ha0.ne' hu0.ne',abs_div,abs_mul,
    abs_of_pos ha0,abs_of_pos hu0]
  have he' : |‖u‖-(rationalNormCenter f R P : ℝ)| ≤ (1/2 : ℝ)^P := by
    rwa [abs_sub_comm]
  calc
    _ = |‖u‖-(rationalNormCenter f R P : ℝ)|/(rationalNormCenter f R P : ℝ) := by field_simp
    _ ≤ (1/2 : ℝ)^P/(‖u‖/2) := div_le_div₀ hε.le he' (by positivity) ha
    _ = _ := by ring

#print axioms rationalNormCenter_error
#print axioms rationalNormalize_error

end
end Maxwell.Continuum.Calibration
