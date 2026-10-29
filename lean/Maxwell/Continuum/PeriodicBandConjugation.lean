import Maxwell.Continuum.PeriodicPhysicalBand
import Maxwell.Continuum.CellBandFourierSymmetry

/-! Schwarz conjugation of the literal physical dielectric band, inherited
from conjugation of the maximal infinite-alias Maxwell graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber

attribute [local irreducible] dielectricBand scaledBand

theorem physicalChart_star {q : Momentum} (hq : q ∈ physicalChart) :
    star q ∈ physicalChart := by
  intro j
  change ‖star (q j)‖ < _
  rw [norm_star]
  exact hq j

theorem unscale_star (q : Momentum) : unscale (star q) = star (unscale q) := by
  funext j
  simp only [unscale, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul', star_inv₀,
    Complex.star_def, Complex.conj_ofReal]

theorem dielectricBand_schwarz {q : Momentum} (hq : q ∈ physicalChart) :
    dielectricBand (star q) = star (dielectricBand q) := by
  rw [dielectricBand_formula, dielectricBand_formula, unscale_star,
    CellBandFourier.scaledBand_schwarz (unscale_mem_chart hq)]
  simp only [star_add, star_mul', star_sub, star_ofNat, Complex.star_def,
    Complex.conj_ofReal]

end Maxwell.Continuum.PeriodicBand
