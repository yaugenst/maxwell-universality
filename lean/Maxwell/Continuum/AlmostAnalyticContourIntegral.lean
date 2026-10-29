import Maxwell.Continuum.AlmostAnalyticContourDerivative
import Maxwell.Continuum.CompactParameterIntegrable

/-! The complete integral contour-movement identity for the literal
smooth cutoff and an operator-valued holomorphic symbol. All support,
differentiation, Fubini and boundary-term conditions are discharged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AlmostAnalytic

open Complex FreeFiber PeriodicBand Auxiliary MeasureTheory Set Metric

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def contourRemainder (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ) (q : Space) : F :=
  cutoffDefect K β s q • Y (shiftedMomentum q β s)

theorem contourRemainder_integrable (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ)
    (hY : ∀ q, ‖q‖ ≤ 4*smallRadius → AnalyticAt ℂ Y (shiftedMomentum q β s)) :
    Integrable (contourRemainder K β Y s) := by
  have hd : Integrable (contourTimeDerivative K β Y s) :=
    (contourTimeDerivative_continuous K β Y s hY).integrable_of_hasCompactSupport
      (contourTimeDerivative_compact K β Y s)
  have hg := contourProduct_contDiff K β Y s hY
  have hgc := contourProduct_compact K β Y s
  have hc : Continuous (fun q => fderiv ℝ (contourProduct K β Y s) q β) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcompact : HasCompactSupport (fun q => fderiv ℝ (contourProduct K β Y s) q β) :=
    (hgc.fderiv ℝ).comp_left (g := fun A : Space →L[ℝ] F => A β) rfl
  have hi : Integrable (fun q => fderiv ℝ (contourProduct K β Y s) q β) :=
    hc.integrable_of_hasCompactSupport hcompact
  have he : contourRemainder K β Y s = fun q => contourTimeDerivative K β Y s q -
      I • fderiv ℝ (contourProduct K β Y s) q β := by
    funext q
    rw [contourProduct_defect_global K β Y s q (hY q)]
    simp only [contourRemainder, add_sub_cancel_left]
  rw [he]
  convert hd.sub (hi.smul I) using 1

theorem contour_integral_identity (K : ℕ) (β : Space) (Y : Momentum → F)
    (hY : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q, ‖q‖ ≤ 4*smallRadius →
      AnalyticAt ℂ Y (shiftedMomentum q β s)) :
    (∫ q, contourProduct K β Y 1 q) - (∫ q, contourProduct K β Y 0 q) =
      ∫ s in (0 : ℝ)..1, ∫ q, contourRemainder K β Y s q := by
  have hD (q : Space) : IntervalIntegrable (fun s => contourTimeDerivative K β Y s q) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (u := fun s => contourTimeDerivative K β Y s q) (by norm_num)
    intro s hs
    have hp : ContinuousAt (fun t : ℝ => (t,q)) s :=
      continuousAt_id.prodMk continuousAt_const
    have hc : ContinuousAt (fun t : ℝ => contourTimeDerivative K β Y t q) s :=
      (contourTimeDerivative_continuousAt K β Y (s,q) (hY s hs q)).comp
        (f := fun t : ℝ => (t,q)) hp
    exact hc.continuousWithinAt
  have hDprod : Integrable (Function.uncurry (contourTimeDerivative K β Y))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume) := by
    apply compact_parameter_integrable _ (isCompact_closedBall (0 : Space) (4*smallRadius))
    · intro p hp
      exact (contourTimeDerivative_continuousAt K β Y p (hY p.1 hp.1 p.2)).continuousWithinAt
    · intro s _ q hq
      apply contourTimeDerivative_zero_outside
      simpa only [mem_closedBall, dist_zero_right, not_le] using hq
  refine compact_transport_identity (contourProduct K β Y) (contourTimeDerivative K β Y)
    (contourRemainder K β Y) β ?_ ?_ hD hDprod ?_ ?_ ?_
  · intro s hs
    exact (contourProduct_contDiff K β Y s (hY s hs)).of_le (by simp)
  · intro s _
    exact contourProduct_compact K β Y s
  · intro s hs
    exact contourRemainder_integrable K β Y s (hY s hs)
  · intro q s hs
    exact contourTimeDerivative_hasDerivAt K β Y s q (hY s hs q)
  · intro s hs q
    exact contourProduct_defect_global K β Y s q (hY s hs q)

#print axioms contour_integral_identity

end Maxwell.Continuum.AlmostAnalytic
