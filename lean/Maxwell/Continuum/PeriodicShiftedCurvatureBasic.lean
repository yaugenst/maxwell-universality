import Maxwell.Continuum.PeriodicTubeTransition
import Maxwell.Continuum.PeriodicBandConjugation
import Maxwell.Continuum.EvenTaylorQuadratic

/-! Symmetry and analyticity of the actual quartic remainder, used to
control real curvature around an imaginary displacement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric

attribute [local irreducible] dielectricBand hessian physicalQuadratic hessianEnergy

def physicalRemainder (p : Momentum) : ℂ :=
  dielectricBand p - dielectricBand 0 - physicalQuadratic p

theorem physicalQuadratic_analyticAt (p : Momentum) : AnalyticAt ℂ physicalQuadratic p := by
  rw [show physicalQuadratic = (fun q : Momentum =>
    ∑ j : Fin 3, (hessian j j : ℂ) * (q j)^2) from funext physicalQuadratic_diagonal]
  exact Finset.analyticAt_fun_sum _ (fun j _ => analyticAt_const.mul
    (((ContinuousLinearMap.proj j : Momentum →L[ℂ] ℂ).analyticAt p).pow 2))

theorem physicalRemainder_analyticAt {p : Momentum} (hp : p ∈ physicalChart) :
    AnalyticAt ℂ physicalRemainder p :=
  ((dielectricBand_analytic p hp).sub analyticAt_const).sub (physicalQuadratic_analyticAt p)

theorem physicalRemainder_norm_le {p : Momentum} (hp : ‖p‖ ≤ analyticRadius / 2) :
    ‖physicalRemainder p‖ ≤ quarticConstant * ‖p‖^4 := physical_quartic hp

theorem hessianEnergy_zero : hessianEnergy 0 = 0 := by
  rw [hessianEnergy_diagonal]
  simp

theorem hessianEnergy_neg (q : Corner.Vec) : hessianEnergy (-q) = hessianEnergy q := by
  rw [hessianEnergy_diagonal, hessianEnergy_diagonal]
  simp only [Pi.neg_apply, neg_sq]

theorem shiftedMomentum_neg_real (q b : Corner.Vec) :
    shiftedMomentum (-q) b = -(star (shiftedMomentum q b)) := by
  funext j
  simp [shiftedMomentum, realMomentum, Complex.ext_iff, Complex.mul_re, Complex.mul_im]

theorem shiftedBand_re_neg (q b : Corner.Vec)
    (hp : shiftedMomentum q b ∈ physicalChart) :
    (dielectricBand (shiftedMomentum (-q) b)).re =
      (dielectricBand (shiftedMomentum q b)).re := by
  rw [shiftedMomentum_neg_real, dielectricBand_neg (physicalChart_star hp),
    dielectricBand_schwarz hp]
  rfl

theorem physicalRemainder_shift_re (q b : Corner.Vec) :
    (physicalRemainder (shiftedMomentum q b)).re =
      (dielectricBand (shiftedMomentum q b)).re - centerEnergy -
        (hessianEnergy q - hessianEnergy b) := by
  simp only [physicalRemainder, Complex.sub_re, shifted_quadratic_re, centerEnergy]

theorem physicalRemainder_shift_re_neg (q b : Corner.Vec)
    (hp : shiftedMomentum q b ∈ physicalChart) :
    (physicalRemainder (shiftedMomentum (-q) b)).re =
      (physicalRemainder (shiftedMomentum q b)).re := by
  rw [physicalRemainder_shift_re, physicalRemainder_shift_re, shiftedBand_re_neg q b hp,
    hessianEnergy_neg]

theorem physicalRemainder_shift_difference_re (q b : Corner.Vec) :
    (physicalRemainder (shiftedMomentum q b) - physicalRemainder (shiftedMomentum 0 b)).re =
      (dielectricBand (shiftedMomentum q b)).re - (dielectricBand (shiftedMomentum 0 b)).re -
        hessianEnergy q := by
  rw [Complex.sub_re, physicalRemainder_shift_re, physicalRemainder_shift_re, hessianEnergy_zero]
  ring

end Maxwell.Continuum.PeriodicBand
