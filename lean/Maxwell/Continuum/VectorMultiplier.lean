import Maxwell.Continuum.KernelIntegral

/-! A bounded measurable vector field gives an actual rectangular
multiplication operator from scalar L² to vector-valued L². -/

noncomputable section

namespace Maxwell.Continuum.VectorMultiplier

open MeasureTheory
open scoped ENNReal

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure Data (μ : Measure X) (C : ℝ) where
  coefficient : X → H
  measurable : AEStronglyMeasurable coefficient μ
  nonneg : 0 ≤ C
  bound : ∀ x, ‖coefficient x‖ ≤ C

namespace Data

variable {μ : Measure X} {C : ℝ} (D : Data (H := H) μ C)

def coefficientLp : Lp H ∞ μ :=
  (memLp_top_of_bound D.measurable C (Filter.Eventually.of_forall D.bound)).toLp _

omit [InnerProductSpace ℂ H] in
theorem coefficientLp_ae : D.coefficientLp =ᵐ[μ] D.coefficient := MemLp.coeFn_toLp _

def operator : Lp ℂ 2 μ →L[ℂ] Lp H 2 μ :=
  ((ContinuousLinearMap.lsmul ℂ ℂ (E := H)).flip.holderL μ ∞ 2 2) D.coefficientLp

theorem operator_ae (f : Lp ℂ 2 μ) :
    D.operator f =ᵐ[μ] fun x => f x • D.coefficient x := by
  have hi := (ContinuousLinearMap.lsmul ℂ ℂ (E := H)).flip.coeFn_holder
    (r := 2) D.coefficientLp f
  filter_upwards [hi, D.coefficientLp_ae] with x hx hv
  exact hx.trans (by simp only [hv, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply])

theorem operator_norm_le : ‖D.operator‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ D.nonneg
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [D.operator_ae f] with x hx
  rw [hx, norm_smul]
  simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (D.bound x) (norm_nonneg (f x))

theorem operator_difference_norm {C' δ : ℝ} (E : Data (H := H) μ C')
    (hδ : 0 ≤ δ) (hDE : ∀ x, ‖D.coefficient x - E.coefficient x‖ ≤ δ) :
    ‖D.operator - E.operator‖ ≤ δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [D.operator_ae f, E.operator_ae f,
    Lp.coeFn_sub (D.operator f) (E.operator f)] with x hd he hs
  change ‖(D.operator f - E.operator f) x‖ ≤ _
  rw [hs, Pi.sub_apply, hd, he, ← smul_sub, norm_smul]
  simpa only [mul_comm δ] using mul_le_mul_of_nonneg_left (hDE x) (norm_nonneg (f x))

end Data
end Maxwell.Continuum.VectorMultiplier
