import Maxwell.Continuum.CellBlochWave

/-! Exact adjoint identities for complex within-cell gauges. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand CellBandFourier MeasureTheory

theorem coefficient_star (q : Momentum) (x : Coordinates) :
    star (coefficient q x) = coefficient (-star q) x := by
  rw [coefficient_apply, coefficient_apply, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_sum, Complex.conj_I, Complex.conj_ofReal,
    Pi.neg_apply, Pi.star_apply, Complex.star_def, neg_mul, Finset.sum_neg_distrib, mul_neg]

theorem gauge_inner (q : Momentum) (f g : CellFieldL2) :
    inner ℂ f (gauge q g) = inner ℂ (gauge (-star q) f) g := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gauge_ae q g j, gauge_ae (-star q) f j] with t hg hf
  rw [hg, hf]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_mul, coefficient_star,
    star_neg, star_star, neg_neg]
  ring

theorem corner_star : star CellGauge.corner = CellGauge.corner := by
  funext j
  exact Complex.conj_ofReal (Real.pi/2)

theorem antiUngauge_inner (q : Momentum) (f g : CellFieldL2) :
    inner ℂ f (antiUngauge q g) = inner ℂ (antiGauge (star q) f) g := by
  rw [antiUngauge_eq, gauge_inner, star_neg, neg_neg, star_add, corner_star, antiGauge_eq]

#print axioms antiUngauge_inner

end Maxwell.Continuum.CellGauge
