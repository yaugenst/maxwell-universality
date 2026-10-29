import Maxwell.Continuum.VectorMultiplier
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The adjoint and full-space Gram operator of the literal bounded
vector multiplier are pointwise inner products and rank-one operators. -/

noncomputable section

namespace Maxwell.Continuum.VectorMultiplier.Data

open MeasureTheory
open scoped ENNReal InnerProduct

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {μ : Measure X} {C : ℝ} (D : VectorMultiplier.Data (H := H) μ C)

def analysisFunction (g : Lp H 2 μ) (x : X) : ℂ := inner ℂ (D.coefficient x) (g x)

theorem analysis_memLp (g : Lp H 2 μ) : MemLp (D.analysisFunction g) 2 μ := by
  apply ((Lp.memLp g).norm.const_mul C).of_le
    (D.measurable.inner (Lp.aestronglyMeasurable g))
  exact Filter.Eventually.of_forall fun x => by
    change ‖inner ℂ (D.coefficient x) (g x)‖ ≤ ‖C * ‖g x‖‖
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg D.nonneg (norm_nonneg _))]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (D.bound x) (norm_nonneg _))

def analysisValue (g : Lp H 2 μ) : Lp ℂ 2 μ := (D.analysis_memLp g).toLp _

theorem analysisValue_ae (g : Lp H 2 μ) :
    D.analysisValue g =ᵐ[μ] fun x => inner ℂ (D.coefficient x) (g x) := MemLp.coeFn_toLp _

theorem analysisValue_norm_le (g : Lp H 2 μ) : ‖D.analysisValue g‖ ≤ C * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [D.analysisValue_ae g] with x hx
  rw [hx]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (D.bound x) (norm_nonneg _))

def analysisLinear : Lp H 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := D.analysisValue
  map_add' f g := by
    apply Lp.ext
    filter_upwards [D.analysisValue_ae (f+g), D.analysisValue_ae f, D.analysisValue_ae g,
      Lp.coeFn_add f g, Lp.coeFn_add (D.analysisValue f) (D.analysisValue g)]
      with x hfg hf hg ha hb
    simp only [hfg, hb, ha, Pi.add_apply, hf, hg, inner_add_right]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [D.analysisValue_ae (c • f), D.analysisValue_ae f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (D.analysisValue f)] with x hcf hf ha hb
    change D.analysisValue (c • f) x = (c • D.analysisValue f) x
    simp only [hcf, hb, ha, Pi.smul_apply, hf, inner_smul_right, smul_eq_mul]

def analysis : Lp H 2 μ →L[ℂ] Lp ℂ 2 μ :=
  D.analysisLinear.mkContinuous C D.analysisValue_norm_le

variable [CompleteSpace H]

theorem operator_eq_analysis_adjoint : D.operator = D.analysis† := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [D.operator_ae f, D.analysisValue_ae g] with x hf hg
  change inner ℂ (D.operator f x) (g x) = inner ℂ (f x) (D.analysisValue g x)
  rw [hf, hg, inner_smul_left]
  change star (f x) * inner ℂ (D.coefficient x) (g x) =
    inner ℂ (D.coefficient x) (g x) * star (f x)
  exact mul_comm _ _

theorem adjoint_ae (g : Lp H 2 μ) :
    (D.operator†) g =ᵐ[μ] fun x => inner ℂ (D.coefficient x) (g x) := by
  rw [D.operator_eq_analysis_adjoint, ContinuousLinearMap.adjoint_adjoint]
  exact D.analysisValue_ae g

theorem gram_ae (g : Lp H 2 μ) :
    D.operator ((D.operator†) g) =ᵐ[μ]
      fun x => (inner ℂ (D.coefficient x) (g x)) • D.coefficient x := by
  filter_upwards [D.operator_ae ((D.operator†) g), D.adjoint_ae g] with x hp ha
  rw [hp, ha]

end Maxwell.Continuum.VectorMultiplier.Data
