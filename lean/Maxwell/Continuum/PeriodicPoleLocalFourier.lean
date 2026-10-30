import Maxwell.Continuum.PeriodicPoleSpaceIntegral
import Maxwell.Continuum.OperatorFourierIntegral

/-! Exact Fourier convention for the local selected pole contribution.
The positive longitudinal phase is the angular transform at -T e_j. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary MeasureTheory OscillatoryPole

theorem angularPhase_longitudinal (j : Fin 3) (T : ℝ) (k : Space) :
    OperatorFourier.angularPhase k (-T • PiLp.single 2 j 1) = oscillatoryPhase T (k j) := by
  unfold OperatorFourier.angularPhase oscillatoryPhase
  rw [real_inner_smul_right]
  have he : inner ℝ k (PiLp.single 2 j 1) = k j := by
    simpa using EuclideanSpace.inner_single_right j (1 : ℝ) k
  rw [he, neg_mul, neg_neg]

theorem localSelectedSymbol_fourier_eq {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (T : ℝ) :
    OperatorFourier.angularFourier (localSelectedSymbol D hh j)
      (-T • PiLp.single 2 j 1) = selectedLocalIntegral D hh j T := by
  rw [OperatorFourier.angularFourier_integral]
  simp only [angularPhase_longitudinal, smul_eq_mul]
  exact selectedLocalSpaceIntegral_eq D hh j T

theorem localSelectedSymbol_fourier_asymptotic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {T : ℝ} (hT : 1 ≤ T) :
    ‖OperatorFourier.angularFourier (localSelectedSymbol D hh j) (-T • PiLp.single 2 j 1)-
      ((selectedGaussianCoefficient D hh j : ℝ) : ℂ)/(T : ℂ)‖ ≤
      (2 : ℝ)^70069/(T*Real.sqrt T) := by
  rw [localSelectedSymbol_fourier_eq]
  exact selectedLocalIntegral_asymptotic D hh j hT

theorem localSelectedSymbol_fourier_placement {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {d : ℝ} (hd : 1 ≤ d) :
    ‖(Real.exp (-poleAction D hh j*d) : ℂ)*
        OperatorFourier.angularFourier (localSelectedSymbol D hh j)
          (-(2*(placementDiagonal j : ℝ)*d) • PiLp.single 2 j 1)-
      (Real.exp (-poleAction D hh j*d) : ℂ)*((selectedLeadingCoefficient D hh j/d : ℝ) : ℂ)‖ ≤
      (2 : ℝ)^70069*Real.exp (-poleAction D hh j*d)/(d*Real.sqrt d) := by
  rw [localSelectedSymbol_fourier_eq]
  exact selectedLocalContribution_asymptotic D hh j hd

#print axioms localSelectedSymbol_fourier_eq
#print axioms localSelectedSymbol_fourier_placement

end Maxwell.Continuum.PeriodicBand
