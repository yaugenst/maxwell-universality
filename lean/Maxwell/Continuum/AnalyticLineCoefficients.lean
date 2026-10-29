import Maxwell.Continuum.EvenTaylor
import Mathlib.Analysis.Analytic.Constructions

/-! The coefficients of a complex line slice are the diagonal evaluations
of the original Fréchet power series. This identifies the actual Hessian,+rather than assigning a quadratic approximation independently of the function. -/

noncomputable section

namespace Maxwell.Continuum.AnalyticLineCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def line (v : E) : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight v

theorem line_apply (v : E) (z : ℂ) : line v z = z • v := rfl

theorem coefficient_eq {f : E → ℂ} {p : FormalMultilinearSeries ℂ E ℂ}
    (hf : HasFPowerSeriesAt f p 0) (v : E) (n : ℕ) :
    EvenTaylor.coefficient (fun z : ℂ => f (z • v)) n = p n (fun _ => v) := by
  have hf' : HasFPowerSeriesAt f p (line v 0) := by
    simpa only [line_apply, zero_smul] using hf
  obtain ⟨r, hr⟩ := hf'.compContinuousLinearMap
  have h := hr.factorial_smul (1 : ℂ) n
  change n.factorial • p n (fun _ => (1 : ℂ) • v) =
    iteratedDeriv n (fun z : ℂ => f (z • v)) 0 at h
  rw [one_smul, nsmul_eq_mul] at h
  unfold EvenTaylor.coefficient
  rw [← h, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_mul]

theorem coefficient_smul {f : E → ℂ} (hf : AnalyticAt ℂ f 0)
    (c : ℂ) (v : E) (n : ℕ) :
    EvenTaylor.coefficient (fun z : ℂ => f (z • (c • v))) n =
      c ^ n * EvenTaylor.coefficient (fun z : ℂ => f (z • v)) n := by
  obtain ⟨p, hp⟩ := hf
  rw [coefficient_eq hp, coefficient_eq hp]
  simp only [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Maxwell.Continuum.AnalyticLineCoefficients
