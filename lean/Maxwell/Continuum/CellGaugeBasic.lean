import Maxwell.Continuum.CompactCoefficientMultiplier
import Maxwell.Continuum.DiagonalMap
import Maxwell.Continuum.CellFourierUnitary
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! The actual bounded within-cell Bloch gauge on the full cell L² space.
The measurable cell representative is retained; analyticity takes place in
the supremum-norm algebra of coefficients before multiplication on L². -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open FreeFiber CellBandFourier MeasureTheory UnitAddTorus Set

abbrev Coordinates := Fin 3 → Icc (0 : ℝ) 2

def cellPoint (t : Torus) : Coordinates := fun j =>
  ⟨2 * ((measurableEquivPiIoc (fun _ : Fin 3 => (0 : ℝ))) t).val j, by
    have hj := ((measurableEquivPiIoc (fun _ : Fin 3 => (0 : ℝ))) t).property j
    constructor <;> linarith [hj.1, hj.2]⟩

theorem cellPoint_measurable : Measurable cellPoint := by
  apply Measurable.of_eval
  intro j
  apply Measurable.subtype_mk
  exact measurable_const.mul ((measurable_pi_apply j).comp
    (measurable_subtype_coe.comp (measurableEquivPiIoc
      (fun _ : Fin 3 => (0 : ℝ))).measurable))

def exponentLinear : Momentum →ₗ[ℂ] C(Coordinates, ℂ) where
  toFun q := ⟨fun x => Complex.I * ∑ j : Fin 3, q j * ((x j).val : ℂ), by fun_prop⟩
  map_add' q p := by
    ext x
    simp only [ContinuousMap.add_apply, ContinuousMap.coe_mk, Pi.add_apply,
      add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c q := by
    ext x
    change Complex.I * (∑ j : Fin 3, (c * q j) * ((x j).val : ℂ)) =
      c * (Complex.I * ∑ j : Fin 3, q j * ((x j).val : ℂ))
    simp only [mul_assoc, ← Finset.mul_sum]
    ring

def exponent : Momentum →L[ℂ] C(Coordinates, ℂ) := exponentLinear.toContinuousLinearMap

theorem exponent_apply (q : Momentum) (x : Coordinates) :
    exponent q x = Complex.I * ∑ j : Fin 3, q j * ((x j).val : ℂ) := rfl

theorem exponent_point_bound (q : Momentum) (x : Coordinates) :
    ‖exponent q x‖ ≤ 6 * ‖q‖ := by
  rw [exponent_apply, norm_mul, Complex.norm_I, one_mul]
  calc
    _ ≤ ∑ j : Fin 3, ‖q j * ((x j).val : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖q‖ * 2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (x j).property.1]
      exact mul_le_mul (norm_le_pi_norm q j) (x j).property.2
        (x j).property.1 (norm_nonneg q)
    _ = 6 * ‖q‖ := by simp; ring

def coefficient (q : Momentum) : C(Coordinates, ℂ) := NormedSpace.exp (exponent q)

theorem coefficient_apply (q : Momentum) (x : Coordinates) :
    coefficient q x = Complex.exp (Complex.I * ∑ j : Fin 3, q j * ((x j).val : ℂ)) := by
  have he := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ x)
    (ContinuousMap.evalCLM ℂ x).continuous (exponent q)
  rw [← Complex.exp_eq_exp_ℂ] at he
  exact he

theorem coefficient_analytic (q : Momentum) : AnalyticAt ℂ coefficient q :=
  (NormedSpace.exp_analytic (𝕂 := ℂ) (exponent q)).comp
    (f := exponent) (exponent.analyticAt q)

theorem coefficient_norm_le (q : Momentum) : ‖coefficient q‖ ≤ Real.exp (6 * ‖q‖) := by
  apply (ContinuousMap.norm_le _ (Real.exp_pos _).le).mpr
  intro x
  rw [coefficient_apply]
  exact (Complex.norm_exp_le_exp_norm _).trans
    (Real.exp_le_exp.mpr (exponent_point_bound q x))

def coefficientMap : C(Coordinates, ℂ) →L[ℂ] (CellFieldL2 →L[ℂ] CellFieldL2) :=
  DiagonalMap.diagonalCLM.comp
    (CompactCoefficient.coefficientMap (μ := torusMeasure) cellPoint cellPoint_measurable)

def gauge (q : Momentum) : CellFieldL2 →L[ℂ] CellFieldL2 := coefficientMap (coefficient q)

theorem gauge_ae (q : Momentum) (u : CellFieldL2) (j : Fin 3) :
    gauge q u j =ᵐ[torusMeasure] fun t => coefficient q (cellPoint t) * u j t :=
  CompactCoefficient.multiplier_ae cellPoint cellPoint_measurable (coefficient q) (u j)

theorem gauge_analytic (q : Momentum) : AnalyticAt ℂ gauge q :=
  (coefficientMap.analyticAt (coefficient q)).comp (f := coefficient) (coefficient_analytic q)

theorem gauge_norm_le (q : Momentum) : ‖gauge q‖ ≤ Real.exp (6 * ‖q‖) := by
  change ‖DiagonalMap.diagonal (CompactCoefficient.multiplier (μ := torusMeasure)
    cellPoint cellPoint_measurable (coefficient q))‖ ≤ _
  exact (DiagonalMap.diagonal_norm_le _).trans
    ((CompactCoefficient.multiplier_norm_le (μ := torusMeasure) cellPoint
      cellPoint_measurable (coefficient q)).trans (coefficient_norm_le q))

#print axioms gauge_ae
#print axioms gauge_analytic
#print axioms gauge_norm_le

end Maxwell.Continuum.CellGauge
