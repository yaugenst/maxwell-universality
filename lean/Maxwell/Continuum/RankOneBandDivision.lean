import Mathlib.Analysis.Analytic.IsolatedZeros
import Maxwell.Continuum.AnalyticFixedPointScalar

/-! Analytic divided differences, including their actual value at the
diagonal, obtained from convergent power series. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand

open scoped Topology ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem analyticAt_dslope_same {f : ℂ → F} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem analyticAt_dslope {f : ℂ → F} {a b : ℂ}
    (ha : AnalyticAt ℂ f a) (hb : AnalyticAt ℂ f b) : AnalyticAt ℂ (dslope f a) b := by
  by_cases h : b = a
  · subst b
    exact analyticAt_dslope_same ha
  · have hi : AnalyticAt ℂ (fun z : ℂ => (z - a)⁻¹) b :=
      (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr h)
    have hs : AnalyticAt ℂ (slope f a) b :=
      (hi.contDiffAt.smul (hb.sub analyticAt_const).contDiffAt).analyticAt
    exact hs.congr (dslope_eventuallyEq_slope_of_ne f h).symm

#print axioms analyticAt_dslope

end Maxwell.Continuum.RankOneBand
