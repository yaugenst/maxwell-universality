import Maxwell.Continuum.FiberL1Space
import Maxwell.Continuum.CellBandFourierReference

/-! Fourier reconstruction is a bounded linear map from the actual full
ℓ¹ alias space into continuous cell fields with the supremum norm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber

theorem periodicSeries_add_l1 (u v : FiberL1.Space) :
    periodicSeries (FiberL1.inclusion (u+v)) =
      periodicSeries (FiberL1.inclusion u) + periodicSeries (FiberL1.inclusion v) := by
  apply (periodicSeries_hasSum (FiberL1.inclusion (u+v)) (FiberL1.summable_norm (u+v))).unique
  have hs := (periodicSeries_hasSum (FiberL1.inclusion u) (FiberL1.summable_norm u)).add
    (periodicSeries_hasSum (FiberL1.inclusion v) (FiberL1.summable_norm v))
  convert hs using 1
  funext ν
  apply ContinuousMap.ext
  intro x
  simp only [mode_apply, ContinuousMap.add_apply, FiberL1.inclusion_apply,
    lp.coeFn_add, Pi.add_apply, smul_add]

theorem periodicSeries_smul_l1 (c : ℂ) (u : FiberL1.Space) :
    periodicSeries (FiberL1.inclusion (c • u)) = c • periodicSeries (FiberL1.inclusion u) := by
  apply (periodicSeries_hasSum (FiberL1.inclusion (c • u)) (FiberL1.summable_norm (c • u))).unique
  have hs := (periodicSeries_hasSum (FiberL1.inclusion u) (FiberL1.summable_norm u)).const_smul c
  convert hs using 1
  funext ν
  apply ContinuousMap.ext
  intro x
  simp only [mode_apply, ContinuousMap.smul_apply, FiberL1.inclusion_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_comm c]

def periodicSeriesL1Linear : FiberL1.Space →ₗ[ℂ] C(Torus, Polarization) where
  toFun u := periodicSeries (FiberL1.inclusion u)
  map_add' := periodicSeries_add_l1
  map_smul' c u := periodicSeries_smul_l1 c u

def periodicSeriesL1 : FiberL1.Space →L[ℂ] C(Torus, Polarization) :=
  periodicSeriesL1Linear.mkContinuous 1 (fun u => by
    change ‖periodicSeries (FiberL1.inclusion u)‖ ≤ 1 * ‖u‖
    rw [one_mul, FiberL1.norm_eq_tsum]
    exact periodicSeries_norm_le (FiberL1.inclusion u) (FiberL1.summable_norm u))

theorem periodicSeriesL1_eq (u : FiberL1.Space) :
    periodicSeriesL1 u = periodicSeries (FiberL1.inclusion u) := rfl

theorem periodicSeriesL1_norm : ‖periodicSeriesL1‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖periodicSeries (FiberL1.inclusion u)‖ ≤ 1 * ‖u‖
  rw [one_mul, FiberL1.norm_eq_tsum]
  exact periodicSeries_norm_le (FiberL1.inclusion u) (FiberL1.summable_norm u)

def cellEvaluationL1 (x : Space) : FiberL1.Space →L[ℂ] Polarization :=
  (Complex.I * carrier x) • ((ContinuousMap.evalCLM ℂ (torusPoint x)).comp periodicSeriesL1)

theorem cellEvaluationL1_eq (x : Space) (u : FiberL1.Space) :
    cellEvaluationL1 x u = Complex.I • antiperiodicField (FiberL1.inclusion u) x := by
  simp only [cellEvaluationL1, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousMap.evalCLM_apply, periodicSeriesL1_eq, antiperiodicField, periodicField, smul_smul]

theorem cellEvaluationL1_norm (x : Space) : ‖cellEvaluationL1 x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [cellEvaluationL1_eq, norm_smul, Complex.norm_I, one_mul, one_mul, FiberL1.norm_eq_tsum]
  exact antiperiodicField_norm_le (FiberL1.inclusion u) (FiberL1.summable_norm u) x

#print axioms periodicSeriesL1_norm
#print axioms cellEvaluationL1_eq

end Maxwell.Continuum.CellBandFourier
