import Maxwell.Continuum.CellGaugeBasic
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Exact inverse and real unitarity of the within-cell gauge, including
the fixed antiperiodic corner carrier. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open FreeFiber CellBandFourier MeasureTheory

theorem coefficient_add (q p : Momentum) : coefficient (q + p) = coefficient q * coefficient p := by
  ext x
  simp only [coefficient_apply, ContinuousMap.mul_apply, Pi.add_apply, add_mul,
    Finset.sum_add_distrib, mul_add, Complex.exp_add]

theorem coefficient_zero : coefficient 0 = 1 := by
  ext x
  simp only [coefficient_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    mul_zero, Complex.exp_zero, ContinuousMap.one_apply]

theorem gauge_add (q p : Momentum) : gauge (q + p) = (gauge q).comp (gauge p) := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [gauge_ae (q+p) u j, gauge_ae q (gauge p u) j, gauge_ae p u j]
    with t hqp hq hp
  change gauge (q+p) u j t = gauge q (gauge p u) j t
  rw [hqp, hq, hp, coefficient_add, ContinuousMap.mul_apply, mul_assoc]

theorem gauge_zero : gauge 0 = ContinuousLinearMap.id ℂ CellFieldL2 := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [gauge_ae 0 u j] with t ht
  change gauge 0 u j t = u j t
  rw [ht, coefficient_zero, ContinuousMap.one_apply, one_mul]

theorem gauge_neg_comp (q : Momentum) :
    (gauge (-q)).comp (gauge q) = ContinuousLinearMap.id ℂ CellFieldL2 := by
  rw [← gauge_add, neg_add_cancel, gauge_zero]

theorem gauge_comp_neg (q : Momentum) :
    (gauge q).comp (gauge (-q)) = ContinuousLinearMap.id ℂ CellFieldL2 := by
  rw [← gauge_add, add_neg_cancel, gauge_zero]

theorem coefficient_real_norm (q : Fin 3 → ℝ) (x : Coordinates) :
    ‖coefficient (realMomentum q) x‖ = 1 := by
  rw [coefficient_apply, Complex.norm_exp]
  simp [realMomentum, Complex.mul_re, Complex.mul_im]

theorem coefficient_real_norm_le (q : Fin 3 → ℝ) : ‖coefficient (realMomentum q)‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro x
  exact (coefficient_real_norm q x).le

theorem gauge_real_norm_le (q : Fin 3 → ℝ) : ‖gauge (realMomentum q)‖ ≤ 1 := by
  change ‖DiagonalMap.diagonal (CompactCoefficient.multiplier (μ := torusMeasure)
    cellPoint cellPoint_measurable (coefficient (realMomentum q)))‖ ≤ _
  exact (DiagonalMap.diagonal_norm_le _).trans
    ((CompactCoefficient.multiplier_norm_le (μ := torusMeasure) cellPoint
      cellPoint_measurable _).trans (coefficient_real_norm_le q))

theorem gauge_real_isometry (q : Fin 3 → ℝ) (u : CellFieldL2) :
    ‖gauge (realMomentum q) u‖ = ‖u‖ := by
  apply le_antisymm
  · simpa only [one_mul] using (gauge (realMomentum q)).le_of_opNorm_le (gauge_real_norm_le q) u
  · have hg : realMomentum (-q) = -realMomentum q := by ext j; simp [realMomentum]
    have hb := (gauge (realMomentum (-q))).le_of_opNorm_le (gauge_real_norm_le (-q))
      (gauge (realMomentum q) u)
    rw [hg, ← ContinuousLinearMap.comp_apply, gauge_neg_comp] at hb
    simpa only [ContinuousLinearMap.id_apply, one_mul] using hb

def corner : Momentum := realMomentum (fun _ => Real.pi / 2)

def antiGauge (q : Momentum) : CellFieldL2 →L[ℂ] CellFieldL2 := (gauge q).comp (gauge corner)
def antiUngauge (q : Momentum) : CellFieldL2 →L[ℂ] CellFieldL2 :=
  (gauge (-corner)).comp (gauge (-q))

theorem antiGauge_eq (q : Momentum) : antiGauge q = gauge (q + corner) := (gauge_add q corner).symm
theorem antiUngauge_eq (q : Momentum) : antiUngauge q = gauge (-(q + corner)) := by
  rw [antiUngauge, ← gauge_add]
  congr 1
  abel

theorem antiUngauge_comp_antiGauge (q : Momentum) :
    (antiUngauge q).comp (antiGauge q) = ContinuousLinearMap.id ℂ CellFieldL2 := by
  rw [antiGauge_eq, antiUngauge_eq, gauge_neg_comp]

theorem antiGauge_comp_antiUngauge (q : Momentum) :
    (antiGauge q).comp (antiUngauge q) = ContinuousLinearMap.id ℂ CellFieldL2 := by
  rw [antiGauge_eq, antiUngauge_eq, gauge_comp_neg]

theorem antiGauge_analytic (q : Momentum) : AnalyticAt ℂ antiGauge q := by
  exact ((gauge_analytic q).contDiffAt.clm_comp contDiffAt_const).analyticAt

theorem antiUngauge_analytic (q : Momentum) : AnalyticAt ℂ antiUngauge q := by
  exact (contDiffAt_const.clm_comp
    (((gauge_analytic (-q)).comp (f := fun p : Momentum => -p) analyticAt_id.neg).contDiffAt)).analyticAt

theorem antiGauge_norm_le (q : Momentum) : ‖antiGauge q‖ ≤ Real.exp (6 * ‖q‖) := by
  calc
    _ ≤ ‖gauge q‖ * ‖gauge corner‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Real.exp (6 * ‖q‖) * 1 := mul_le_mul (gauge_norm_le q)
      (gauge_real_norm_le (fun _ => Real.pi / 2)) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := mul_one _

theorem antiUngauge_norm_le (q : Momentum) : ‖antiUngauge q‖ ≤ Real.exp (6 * ‖q‖) := by
  have hc : -corner = realMomentum (fun _ : Fin 3 => -(Real.pi / 2)) := by
    ext j
    simp [corner, realMomentum]
  calc
    _ ≤ ‖gauge (-corner)‖ * ‖gauge (-q)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * Real.exp (6 * ‖q‖) := mul_le_mul
      (by rw [hc]; exact gauge_real_norm_le _) (by simpa using gauge_norm_le (-q))
      (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

theorem antiGauge_ae (q : Momentum) (u : CellFieldL2) (j : Fin 3) :
    antiGauge q u j =ᵐ[torusMeasure] fun t =>
      Complex.exp (Complex.I * ∑ k : Fin 3,
        (q k + (Real.pi / 2 : ℂ)) * ((cellPoint t k).val : ℂ)) * u j t := by
  rw [antiGauge_eq]
  filter_upwards [gauge_ae (q+corner) u j] with t ht
  rw [ht, coefficient_apply]
  simp only [Pi.add_apply, corner, realMomentum, Complex.ofReal_div, Complex.ofReal_ofNat]

#print axioms antiUngauge_comp_antiGauge
#print axioms gauge_real_isometry
#print axioms antiGauge_ae

end Maxwell.Continuum.CellGauge
