import Maxwell.Continuum.CouplingAbsorption
import Maxwell.Continuum.PeriodicPoleLocalPlacement

/-! The manuscript's useful-coupling lower bound from the constructed
imaginary action, actual positive leading coefficient, and explicit errors.
The remaining hypothesis here is the coupling asymptotic, supplied by the
physical source Fourier/contour decomposition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open Auxiliary MasterConstants

attribute [local irreducible] selectedLeadingCoefficient poleAction

theorem eight_rpow_negative (d : ℝ) : (8 : ℝ)^(-d) = Real.exp (-Real.log 8*d) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 8)]
  congr 1
  ring

theorem usefulCoupling_lower_of_master_remainder {L z d : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (j : Fin 3) {J : ℂ}
    (hd : ds ≤ d) (hspace : Cs^4*L ≤ d^15)
    (htail : Cs*L^5*Real.exp (-cs*L) ≤ (cu/4)*L^2*(8 : ℝ)^(-d))
    (herr : ‖J-((L^2*Real.exp (-poleAction D (inverse_length_le_1024 hL) j*d)*
        selectedLeadingCoefficient D (inverse_length_le_1024 hL) j/d : ℝ) : ℂ)‖ ≤
      Cs*L^2*Real.exp (-poleAction D (inverse_length_le_1024 hL) j*d)/(d*Real.sqrt d) +
        Cs*L^3*Real.exp (-poleAction D (inverse_length_le_1024 hL) j*d)/d^16 +
        Cs*L^5*Real.exp (-cs*L)) :
    cu*L^2*(8 : ℝ)^(-d) ≤ J.re := by
  rw [eight_rpow_negative] at htail ⊢
  exact coupling_lower_of_green_remainder hd hspace
    (selectedLeadingCoefficient_paper_lower D (inverse_length_le_1024 hL) j)
    (poleAction_log_margin D (inverse_length_le_1024 hL) j).le htail herr

theorem usefulCoupling_lower_of_explicit_remainder {L z d : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (j : Fin 3) {J : ℂ}
    (hd : ds ≤ d) (hspace : Cs^4*L ≤ d^15)
    (htail : Cs*L^5*Real.exp (-cs*L) ≤ (cu/4)*L^2*(8 : ℝ)^(-d))
    (herr : ‖J-((L^2*Real.exp (-poleAction D (inverse_length_le_1024 hL) j*d)*
        selectedLeadingCoefficient D (inverse_length_le_1024 hL) j/d : ℝ) : ℂ)‖ ≤
      (2 : ℝ)^70069*L^2*Real.exp (-poleAction D (inverse_length_le_1024 hL) j*d)/(d*Real.sqrt d) +
        2*((2 : ℝ)^220000*L^3*Real.exp (-poleAction D (inverse_length_le_1024 hL) j*d)/d^16) +
        (2 : ℝ)^341*L^3*Real.exp (-cs*L)) :
    cu*L^2*(8 : ℝ)^(-d) ≤ J.re := by
  rw [eight_rpow_negative] at htail ⊢
  exact coupling_lower_of_explicit_remainder hL hd hspace
    (selectedLeadingCoefficient_paper_lower D (inverse_length_le_1024 hL) j)
    (poleAction_log_margin D (inverse_length_le_1024 hL) j).le htail herr

#print axioms usefulCoupling_lower_of_explicit_remainder

end Maxwell.Continuum.PeriodicBand
