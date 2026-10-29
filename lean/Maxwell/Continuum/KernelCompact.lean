import Maxwell.Continuum.KernelIntegral
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Compactness of the literal L² kernel integral operator. The proof uses
the proved density of simple functions and closure of compact operators
in operator norm. -/

noncomputable section

namespace Maxwell.Continuum.KernelIntegral

open MeasureTheory
open scoped ENNReal

variable {X E : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem operator_indicator (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    operator μ (indicatorConstLp 2 hs hμs c) =
      (ContinuousLinearMap.toSpanSingleton ℂ c).comp
        (operator μ (indicatorConstLp 2 hs hμs (1 : ℂ))) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [operator_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, operator_apply, ← integral_smul_const]
  apply integral_congr_ae
  filter_upwards [@indicatorConstLp_coeFn X E _ 2 μ _ s hs hμs c,
    @indicatorConstLp_coeFn X ℂ _ 2 μ _ s hs hμs 1] with x hx hy
  rw [hx, hy]
  by_cases h : x ∈ s <;> simp [h]

theorem operator_indicator_compact (s : Set X) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : E) :
    IsCompactOperator (operator μ (indicatorConstLp 2 hs hμs c)) := by
  rw [operator_indicator]
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ c)).comp_clm _

theorem operator_compact (k : Lp E 2 μ) : IsCompactOperator (operator μ k) := by
  apply Lp.induction (by norm_num : (2 : ENNReal) ≠ ∞)
    (fun k : Lp E 2 μ => IsCompactOperator (operator μ k)) _ _ _ k
  · intro c s hs hμs
    exact operator_indicator_compact μ s hs hμs.ne c
  · intro f g _ _ _ hf hg
    rw [map_add]
    exact hf.add hg
  · exact isClosed_setOfPred_isCompactOperator.preimage (operator μ).continuous

end Maxwell.Continuum.KernelIntegral
