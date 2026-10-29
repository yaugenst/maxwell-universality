import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space

/-! The actual integral operator associated with a square-integrable,
Hilbert-space-valued kernel. The construction is continuous in its kernel,
with the sharp elementary Hilbert--Schmidt norm bound. -/

noncomputable section

namespace Maxwell.Continuum.KernelIntegral

open MeasureTheory

variable {X E : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def operator : Lp E 2 μ →L[ℂ] (Lp ℂ 2 μ →L[ℂ] E) :=
  (ContinuousLinearMap.lsmul ℂ ℂ (E := E)).flip.lpPairing μ 2 2

theorem operator_apply (k : Lp E 2 μ) (f : Lp ℂ 2 μ) :
    operator μ k f = ∫ x, f x • k x ∂μ := by
  exact ContinuousLinearMap.lpPairing_eq_integral _ k f

omit [CompleteSpace E] in
theorem integrable_apply (k : Lp E 2 μ) (f : Lp ℂ 2 μ) :
    Integrable (fun x => f x • k x) μ :=
  memLp_one_iff_integrable.mp ((Lp.memLp f).smul (Lp.memLp k))

theorem operator_apply_norm (k : Lp E 2 μ) (f : Lp ℂ 2 μ) :
    ‖operator μ k f‖ ≤ ‖k‖ * ‖f‖ := by
  have he : operator μ k f = L1.integral (f • k : Lp E 1 μ) := by
    rw [operator_apply, L1.integral_eq_integral]
    exact integral_congr_ae (Lp.coeFn_lpSMul f k).symm
  rw [he]
  exact (L1.norm_integral_le _).trans ((Lp.norm_smul_le f k).trans_eq (mul_comm _ _))

theorem operator_norm (k : Lp E 2 μ) : ‖operator μ k‖ ≤ ‖k‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (operator_apply_norm μ k)

theorem operator_map_norm : ‖operator μ (E := E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro k
  simpa only [one_mul] using operator_norm μ k

theorem operator_difference_norm (k l : Lp E 2 μ) :
    ‖operator μ k - operator μ l‖ ≤ ‖k - l‖ := by
  rw [← map_sub]
  exact operator_norm μ (k - l)

end Maxwell.Continuum.KernelIntegral
