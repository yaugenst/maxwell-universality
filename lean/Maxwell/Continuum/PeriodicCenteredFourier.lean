import Maxwell.Continuum.PeriodicCenteredLift
import Maxwell.Continuum.PeriodicSamplingReconstruction

/-! The Fourier coefficients of the literal centered periodic extension
are the full Euclidean Fourier integrals of the compactly supported symbol. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicSampling

open UnitAddTorus MeasureTheory Set
open scoped Classical

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem centeredLift_coefficient (f : (ι → ℝ) → E) (hc : Continuous f)
    (hf : ∀ x, (∃ i, (1/4 : ℝ) ≤ |x i|) → f x = 0) (n : ι → ℤ) :
    mFourierCoeff (centeredContinuousLift f hc hf) n =
      ∫ x : ι → ℝ, Product.phase (-n) x • f x := by
  rw [mFourierCoeff_eq_integral _ n (fun _ => -(1/2 : ℝ))]
  have hset : MeasurableSet {x : ι → ℝ | ∀ i, x i ∈ Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ)+1)} :=
    MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  calc
    _ = ∫ x : ι → ℝ in {x | ∀ i, x i ∈ Ioc (-(1/2 : ℝ)) (-(1/2 : ℝ)+1)},
        Product.phase (-n) x • f x := by
      apply setIntegral_congr_fun hset
      intro x hx
      have hr : ∀ i, x i ∈ Ioc (-(1/2 : ℝ)) (1/2 : ℝ) := by
        simpa only [Set.mem_ofPred_eq, show -(1/2 : ℝ)+1 = 1/2 by norm_num] using hx
      change mFourier (-n) (fun i => (x i : UnitAddCircle)) •
        centeredLift f (fun i => (x i : UnitAddCircle)) = _
      rw [centeredLift_real f x hr]
      exact congrArg (fun c : ℂ => c • f x) (Product.phase_monomial (-n) x).symm
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hn : ∃ i, x i ∉ Ioc (-(1/2 : ℝ)) (1/2 : ℝ) := by
        simpa only [Set.mem_ofPred_eq, show -(1/2 : ℝ)+1 = 1/2 by norm_num, not_forall] using hx
      obtain ⟨i, hi⟩ := hn
      have hi' : (1/4 : ℝ) ≤ |x i| := by
        rw [mem_Ioc, not_and_or] at hi
        rcases hi with hi | hi
        · have h := le_of_not_gt hi
          rw [abs_of_nonpos (by linarith)]
          linarith
        · have h := lt_of_not_ge hi
          rw [abs_of_nonneg (by linarith)]
          linarith
      rw [hf x ⟨i, hi'⟩, smul_zero]

#print axioms centeredLift_coefficient

end Maxwell.Continuum.PeriodicSampling
