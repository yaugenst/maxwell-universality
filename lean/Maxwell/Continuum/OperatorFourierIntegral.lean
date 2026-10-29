import Maxwell.Continuum.OperatorFourierDecay

/-! Exact angular Fourier integral and its bounded Hilbert-space matrix
elements. All integrability hypotheses concern the full operator norm. -/

noncomputable section

namespace Maxwell.Continuum.OperatorFourier

open MeasureTheory FourierTransform

def angularPhase (q p : Space) : ℂ :=
  Complex.exp ((-inner ℝ q p : ℝ) * Complex.I)

theorem angularPhase_norm (q p : Space) : ‖angularPhase q p‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem angularFourier_integral (f : Space → F) (p : Space) :
    angularFourier f p = ∫ q, angularPhase q p • f q := by
  rw [angularFourier, Real.fourier_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q => by
    dsimp only
    unfold angularPhase
    congr 2
    rw [inner_smul_right]
    push_cast
    field_simp

theorem angularPhase_integrable {f : Space → F} (hf : Integrable f) (p : Space) :
    Integrable (fun q => angularPhase q p • f q) := by
  have hm : Continuous (fun q => angularPhase q p) := by unfold angularPhase; fun_prop
  apply hf.norm.mono' (hm.aestronglyMeasurable.smul hf.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun q => by
    change ‖angularPhase q p • f q‖ ≤ ‖f q‖
    rw [norm_smul, angularPhase_norm, one_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem angularFourier_pairing (A : Space → H →L[ℂ] H) (hA : Integrable A)
    (p : Space) (g f : H) :
    inner ℂ g (angularFourier A p f) =
      ∫ q, angularPhase q p * inner ℂ g (A q f) := by
  let L : (H →L[ℂ] H) →L[ℂ] ℂ :=
    (innerSL ℂ g).comp (ContinuousLinearMap.apply ℂ H f)
  have he := L.integral_comp_comm (angularPhase_integrable hA p)
  rw [angularFourier_integral]
  calc
    _ = L (∫ q, angularPhase q p • A q) := rfl
    _ = ∫ q, L (angularPhase q p • A q) := he.symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by
        dsimp only
        rw [map_smul]
        rfl

#print axioms angularFourier_pairing

end Maxwell.Continuum.OperatorFourier
