import Maxwell.Continuum.PeriodicSamplingProductTail
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Module.Dual

/-! Absolute Fourier reconstruction and exact finite-grid aliasing for
Banach-valued continuous symbols on a finite-dimensional torus. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicSampling.Product

open UnitAddTorus MeasureTheory
open scoped Classical

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem monomial_norm (n : ι → ℤ) (x : UnitAddTorus ι) : ‖mFourier n x‖ = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe,
    Finset.prod_const_one]

def dualFunction (f : C(UnitAddTorus ι, E)) (ℓ : E →L[ℂ] ℂ) : C(UnitAddTorus ι, ℂ) :=
  ⟨fun x => ℓ (f x), ℓ.continuous.comp f.continuous⟩

theorem coefficient_dual (f : C(UnitAddTorus ι, E)) (ℓ : E →L[ℂ] ℂ) (n : ι → ℤ) :
    mFourierCoeff (dualFunction f ℓ) n = ℓ (mFourierCoeff f n) := by
  have hi : Integrable (fun x : UnitAddTorus ι => mFourier (-n) x • f x) :=
    ((mFourier (-n)).continuous.smul f.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he := ℓ.integral_comp_comm hi
  simpa only [mFourierCoeff, dualFunction, ContinuousMap.coe_mk, map_smul] using he

theorem reconstruction (f : C(UnitAddTorus ι, E))
    (hf : Summable (fun n : ι → ℤ => ‖mFourierCoeff f n‖)) (x : UnitAddTorus ι) :
    (∑' n : ι → ℤ, mFourier n x • mFourierCoeff f n) = f x := by
  have hs : Summable (fun n : ι → ℤ => mFourier n x • mFourierCoeff f n) := by
    apply Summable.of_norm_bounded hf
    intro n
    simp only [norm_smul, monomial_norm, one_mul, le_refl]
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro ℓ
  have hc : Summable (mFourierCoeff (dualFunction f ℓ)) := by
    convert! ℓ.summable hf.of_norm using 1
    funext n
    exact coefficient_dual f ℓ n
  have he := (hasSum_mFourier_series_apply_of_summable hc x).tsum_eq
  rw [ℓ.map_tsum hs]
  calc
    _ = ∑' n : ι → ℤ, mFourierCoeff (dualFunction f ℓ) n • mFourier n x := by
      apply tsum_congr
      intro n
      rw [map_smul, coefficient_dual]
      exact mul_comm _ _
    _ = _ := he

theorem phase_monomial (n : ι → ℤ) (x : ι → ℝ) :
    phase n x = mFourier n (fun i => (x i : UnitAddCircle)) := by
  unfold phase mFourier
  apply Finset.prod_congr rfl
  intro i _
  simp only [PeriodicSampling.phase, fourier_coe_apply, Complex.ofReal_one, div_one]

theorem synthesis_coefficients (f : C(UnitAddTorus ι, E))
    (hf : Summable (fun n : ι → ℤ => ‖mFourierCoeff f n‖)) (x : ι → ℝ) :
    synthesis (mFourierCoeff f) x = f (fun i => (x i : UnitAddCircle)) := by
  unfold synthesis
  simp_rw [phase_monomial]
  exact reconstruction f hf _

theorem coefficient_continuous_samples (N : ℕ) [NeZero N] (f : C(UnitAddTorus ι, E))
    (hf : Summable (fun n : ι → ℤ => ‖mFourierCoeff f n‖)) (k : ι → ℤ) :
    coefficient N (fun j => f (fun i => ((((j i).val : ℝ)/(N : ℝ) : ℝ) : UnitAddCircle))) (frequency N k) =
      ∑' n : ι → ℤ, if frequency N n = frequency N k then mFourierCoeff f n else 0 := by
  simpa only [synthesis_coefficients f hf] using coefficient_samples N (mFourierCoeff f) hf k

#print axioms reconstruction
#print axioms coefficient_continuous_samples

end Maxwell.Continuum.PeriodicSampling.Product
