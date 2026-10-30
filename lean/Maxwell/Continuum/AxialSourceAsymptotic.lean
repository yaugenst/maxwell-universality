import Maxwell.Continuum.AxialSourceContour
import Maxwell.Continuum.FullSourceFourierAsymptotic
import Maxwell.Continuum.PeriodicCouplingLower

/-! The useful nearest-neighbor coupling estimate for the literal
continuum Maxwell resolvent, with no analytic estimate left as a premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open FreeFiber Auxiliary PeriodicBand EffectiveMass MasterConstants

attribute [local irreducible] realMode axialSourceCoupling
  selectedLeadingCoefficient poleAction

theorem axialSourceCoupling_asymptotic {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (hLe : Even L) (D : Calibration (L : ℝ)⁻¹ z) (j : Fin 3) {d : ℕ} (hd : 1 ≤ d) :
    ‖axialSourceCoupling D (inverse_length_le_1024 hL) j (d : ℝ)-
      (((L : ℝ)^2*Real.exp (-poleAction D (inverse_length_le_1024 hL) j*(d : ℝ))*
        selectedLeadingCoefficient D (inverse_length_le_1024 hL) j/(d : ℝ) : ℝ) : ℂ)‖ ≤
      (2 : ℝ)^70069*(L : ℝ)^2*Real.exp (-poleAction D (inverse_length_le_1024 hL) j*(d : ℝ))/
        ((d : ℝ)*Real.sqrt (d : ℝ)) +
      2*((2 : ℝ)^220000*(L : ℝ)^3*Real.exp (-poleAction D (inverse_length_le_1024 hL) j*(d : ℝ))/(d : ℝ)^16) +
      (2 : ℝ)^341*(L : ℝ)^3*Real.exp (-cs*(L : ℝ)) := by
  let hh := inverse_length_le_1024 hL
  let R : Space := -(2*(placementDiagonal j : ℝ)*(d : ℝ)) • PiLp.single 2 j 1
  let E : ℝ := Real.exp (-poleAction D hh j*(d : ℝ))
  let b : ℝ := selectedLeadingCoefficient D hh j
  let F : ℂ := OperatorFourier.angularFourier (fullSourceSymbol D hh j) R
  have hglobal := fullSourceSymbol_fourier_placement D hh j (d := (d : ℝ)) (by exact_mod_cast hd)
  have hfourier : ‖(((L : ℝ)^2*E : ℝ) : ℂ)*F-
      (((L : ℝ)^2*E*b/(d : ℝ) : ℝ) : ℂ)‖ ≤
      (2 : ℝ)^70069*(L : ℝ)^2*E/((d : ℝ)*Real.sqrt (d : ℝ)) +
        2*((2 : ℝ)^220000*(L : ℝ)^3*E/(d : ℝ)^16) := by
    have he (l e b t : ℝ) (f : ℂ) :
        ((l^2*e : ℝ) : ℂ)*f-((l^2*e*b/t : ℝ) : ℂ) =
          ((l^2 : ℝ) : ℂ)*((e : ℂ)*f-(e : ℂ)*((b/t : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hm := mul_le_mul_of_nonneg_left hglobal (sq_nonneg (L : ℝ))
    have halg (A B l e t s : ℝ) :
        l^2*(A*e/(t*s)+2*(B*l*e/t^16)) =
          A*l^2*e/(t*s)+2*(B*l^3*e/t^16) := by ring
    simpa only [inv_inv, halg] using hm
  have hcontour := axialSourceCoupling_scaled_error hL hLe D j d
  change ‖axialSourceCoupling D hh j (d : ℝ)-(((L : ℝ)^2*E : ℝ) : ℂ)*F‖ ≤
    (2 : ℝ)^341*(L : ℝ)^3*Real.exp (-cs*(L : ℝ)) at hcontour
  exact (norm_sub_le_norm_sub_add_norm_sub _ ((((L : ℝ)^2*E : ℝ) : ℂ)*F) _).trans
    ((add_le_add hcontour hfourier).trans_eq (add_comm _ _))

theorem axialSourceCoupling_lower {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (hLe : Even L) (D : Calibration (L : ℝ)⁻¹ z) (j : Fin 3) {d : ℕ}
    (hd : ds ≤ (d : ℝ)) (hspace : Cs^4*(L : ℝ) ≤ (d : ℝ)^15)
    (htail : Cs*(L : ℝ)^5*Real.exp (-cs*(L : ℝ)) ≤
      (cu/4)*(L : ℝ)^2*(8 : ℝ)^(-(d : ℝ))) :
    cu*(L : ℝ)^2*(8 : ℝ)^(-(d : ℝ)) ≤
      (axialSourceCoupling D (inverse_length_le_1024 hL) j (d : ℝ)).re := by
  apply usefulCoupling_lower_of_explicit_remainder hL D j hd hspace htail
  exact axialSourceCoupling_asymptotic hL hLe D j (by exact_mod_cast spacing_ge_one hd)

#print axioms axialSourceCoupling_asymptotic
#print axioms axialSourceCoupling_lower

end Maxwell.Continuum.CellGauge
