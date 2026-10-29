import Maxwell.Continuum.AlmostAnalyticTaylor

/-! Holomorphic factors cancel from the transport derivative. Only
the exact finite-cutoff defect remains, also for operator-valued factors. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AlmostAnalytic

open Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem taylor_holomorphic_defect (K : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (Y : ℂ → F) (x s : ℝ)
    (hY : DifferentiableAt ℂ Y ((x : ℂ)+I*(s : ℂ))) :
    deriv (fun t : ℝ => taylor K f x t • Y ((x : ℂ)+I*(t : ℂ))) s -
      I • deriv (fun y : ℝ => taylor K f y s • Y ((y : ℂ)+I*(s : ℂ))) x =
      (-I * coefficient K s * ((iteratedDeriv (K+1) f x : ℝ) : ℂ)) •
        Y ((x : ℂ)+I*(s : ℂ)) := by
  have hys : HasDerivAt (fun t : ℝ => Y ((x : ℂ)+I*(t : ℂ)))
      (I • deriv Y ((x : ℂ)+I*(s : ℂ))) s := by
    have hd := hY.hasDerivAt.scomp s
      (((hasDerivAt_id s).ofReal_comp.const_mul I).const_add (x : ℂ))
    simpa only [Function.comp_def, id_eq, Complex.ofReal_one, mul_one] using hd
  have hyx : HasDerivAt (fun y : ℝ => Y ((y : ℂ)+I*(s : ℂ)))
      (deriv Y ((x : ℂ)+I*(s : ℂ))) x := by
    have hd := hY.hasDerivAt.scomp x
      ((hasDerivAt_id x).ofReal_comp.add_const (I*(s : ℂ)))
    simpa only [Function.comp_def, id_eq, Complex.ofReal_one, one_smul] using hd
  have hcs := (taylor_hasDerivAt_s K f x s)
  have hcx := (taylor_hasDerivAt_x K f hf x s)
  have hs := hcs.smul hys
  have hx := hcx.smul hyx
  change HasDerivAt (fun t : ℝ => taylor K f x t • Y ((x : ℂ)+I*(t : ℂ))) _ s at hs
  change HasDerivAt (fun y : ℝ => taylor K f y s • Y ((y : ℂ)+I*(s : ℂ))) _ x at hx
  calc
    _ = (deriv (fun t => taylor K f x t) s -
        I * deriv (fun y => taylor K f y s) x) • Y ((x : ℂ)+I*(s : ℂ)) := by
      rw [hs.deriv, hx.deriv, hcs.deriv, hcx.deriv]
      module
    _ = _ := by rw [taylor_defect K f hf]

end Maxwell.Continuum.AlmostAnalytic
