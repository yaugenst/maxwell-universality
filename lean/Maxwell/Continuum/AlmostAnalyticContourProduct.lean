import Maxwell.Continuum.AlmostAnalyticHolomorphic
import Maxwell.Continuum.AlmostAnalyticSupport
import Maxwell.Continuum.SeparatedSymbolDerivatives
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! The exact transport defect for the actual three-dimensional cutoff
multiplied by a holomorphic continuum symbol. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AlmostAnalytic

open Complex FreeFiber PeriodicBand Auxiliary

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

def shiftedMomentum (q β : Space) (s : ℝ) : Momentum :=
  realMomentumMap q + (I*(s : ℂ)) • realMomentumMap β

def contourProduct (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ) (q : Space) : F :=
  cutoffTaylor K smallRadius q β s • Y (shiftedMomentum q β s)

theorem shiftedMomentum_line (q β : Space) (x s : ℝ) :
    realMomentumMap q + ((x : ℂ)+I*(s : ℂ)) • realMomentumMap β =
      shiftedMomentum (q+x • β) β s := by
  rw [shiftedMomentum, map_add, map_smul, add_smul]
  change realMomentumMap q + (x • realMomentumMap β + (I*(s : ℂ)) • realMomentumMap β) = _
  exact (add_assoc _ _ _).symm

theorem contourProduct_differentiableAt (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ) (q : Space)
    (hY : DifferentiableAt ℂ Y (shiftedMomentum q β s)) :
    DifferentiableAt ℝ (contourProduct K β Y s) q := by
  have hp : DifferentiableAt ℝ (fun p : Space => shiftedMomentum p β s) q :=
    realMomentumMap.differentiableAt.add_const _
  exact (cutoffTaylor_contDiff K β s).differentiable (by simp) q |>.smul
    ((hY.restrictScalars ℝ).comp q hp)

theorem contourProduct_defect (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ) (q : Space)
    (hY : DifferentiableAt ℂ Y (shiftedMomentum q β s)) :
    deriv (fun t : ℝ => contourProduct K β Y t q) s -
      I • fderiv ℝ (contourProduct K β Y s) q β =
        cutoffDefect K β s q • Y (shiftedMomentum q β s) := by
  let f : ℝ → ℝ := fun x => Well.chi smallRadius (q+x • β)
  let Z : ℂ → F := fun z => Y (realMomentumMap q+z • realMomentumMap β)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (Well.chi_contDiff smallRadius).comp (by fun_prop)
  have hZ : DifferentiableAt ℂ Z ((0 : ℝ)+I*(s : ℂ)) := by
    have hp : DifferentiableAt ℂ (fun z : ℂ => realMomentumMap q+z • realMomentumMap β)
        (I*(s : ℂ)) := by fun_prop
    simpa only [ofReal_zero, zero_add, Function.comp_def, Z] using hY.comp (I*(s : ℂ)) hp
  have he := taylor_holomorphic_defect K f hf Z 0 s hZ
  have hG := contourProduct_differentiableAt K β Y s q hY
  have hline : deriv (fun t : ℝ => contourProduct K β Y s (q+t • β)) 0 =
      fderiv ℝ (contourProduct K β Y s) q β := hG.lineDeriv_eq_fderiv
  have hs (t : ℝ) : taylor K f 0 t • Z ((0 : ℝ)+I*(t : ℂ)) = contourProduct K β Y t q := by
    have hc := cutoffTaylor_eq_taylor K smallRadius q β 0 t
    simp only [zero_smul, add_zero] at hc
    rw [← hc]
    simp only [Z, ofReal_zero, zero_add, contourProduct, shiftedMomentum]
  have hx (x : ℝ) : taylor K f x s • Z ((x : ℂ)+I*(s : ℂ)) =
      contourProduct K β Y s (q+x • β) := by
    rw [← cutoffTaylor_eq_taylor K smallRadius q β x s]
    unfold Z contourProduct
    rw [shiftedMomentum_line]
  have hd : iteratedDeriv (K+1) f 0 = cutoffDerivative (K+1) β q := by
    simpa only [zero_smul, add_zero, cutoffDerivative] using
      cutoff_line_derivative (K+1) smallRadius q β 0
  simp_rw [hs, hx, hline, hd] at he
  simpa only [Z, ofReal_zero, zero_add, cutoffDefect, shiftedMomentum] using he

#print axioms contourProduct_defect

end Maxwell.Continuum.AlmostAnalytic
