import Maxwell.Continuum.FiberNormalizationNormalized
import Mathlib.Analysis.Fourier.AddCircleMulti

/-! The cell Fourier series is a genuine uniformly convergent vector
series on the unit torus. Physical period two is obtained by evaluating
at `x / 2`; the antiperiodic carrier is supplied separately. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber FiberNormalization UnitAddTorus Filter PeriodicBand
open scoped Topology

abbrev Torus := UnitAddTorus (Fin 3)

def mode (ν : Alias) (a : Polarization) : C(Torus, Polarization) where
  toFun x := mFourier ν x • a
  continuous_toFun := (mFourier ν).continuous.smul continuous_const

@[simp] theorem mode_apply (ν : Alias) (a : Polarization) (x : Torus) :
    mode ν a x = mFourier ν x • a := rfl

theorem monomial_norm (ν : Alias) (x : Torus) : ‖mFourier ν x‖ = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe,
    Finset.prod_const_one]

theorem mode_apply_norm (ν : Alias) (a : Polarization) (x : Torus) :
    ‖mode ν a x‖ = ‖a‖ := by rw [mode_apply, norm_smul, monomial_norm, one_mul]

theorem mode_norm (ν : Alias) (a : Polarization) : ‖mode ν a‖ = ‖a‖ := by
  apply le_antisymm
  · exact (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun x => (mode_apply_norm ν a x).le
  · exact (mode_apply_norm ν a 0).symm.le.trans ((mode ν a).norm_coe_le_norm 0)

def periodicSeries (u : FiberSpace) : C(Torus, Polarization) := ∑' ν, mode ν (u ν)

theorem modes_summable_norm (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) :
    Summable (fun ν => ‖mode ν (u ν)‖) := by simpa only [mode_norm] using hu

theorem periodicSeries_hasSum (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) :
    HasSum (fun ν => mode ν (u ν)) (periodicSeries u) :=
  (modes_summable_norm u hu).of_norm.hasSum

theorem periodicSeries_apply_hasSum (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖))
    (x : Torus) : HasSum (fun ν => mFourier ν x • u ν) (periodicSeries u x) := by
  have h := (ContinuousMap.evalCLM (M := Polarization) ℂ x).hasSum
    (periodicSeries_hasSum u hu)
  exact h

theorem periodicSeries_apply_tsum (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖))
    (x : Torus) : periodicSeries u x = ∑' ν, mFourier ν x • u ν :=
  (periodicSeries_apply_hasSum u hu x).tsum_eq.symm

/-- Convergence in the supremum norm gives a single finite tail bound
valid at every spatial point. -/
theorem periodicSeries_uniform (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : Finset Alias in atTop, ∀ x : Torus,
      ‖(∑ ν ∈ s, mFourier ν x • u ν) - periodicSeries u x‖ < ε := by
  have h := (Metric.tendsto_nhds.mp (periodicSeries_hasSum u hu)) ε hε
  filter_upwards [h] with s hs x
  have hn := ((∑ ν ∈ s, mode ν (u ν)) - periodicSeries u).norm_coe_le_norm x
  have he : ((∑ ν ∈ s, mode ν (u ν)) - periodicSeries u) x =
      (∑ ν ∈ s, mFourier ν x • u ν) - periodicSeries u x := by
    simp only [ContinuousMap.sub_apply, ContinuousMap.sum_apply, mode_apply]
  rw [he] at hn
  exact hn.trans_lt (by simpa only [dist_eq_norm] using hs)

theorem periodicSeries_norm_le (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) :
    ‖periodicSeries u‖ ≤ ∑' ν, ‖u ν‖ := by
  exact (norm_tsum_le_tsum_norm (modes_summable_norm u hu)).trans_eq
    (tsum_congr fun ν => mode_norm ν (u ν))

theorem periodicSeries_apply_norm_le (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖))
    (x : Torus) : ‖periodicSeries u x‖ ≤ ∑' ν, ‖u ν‖ :=
  ((periodicSeries u).norm_coe_le_norm x).trans (periodicSeries_norm_le u hu)

def bandPeriodic (t : Momentum) : C(Torus, Polarization) :=
  periodicSeries (normalizedFiberVector t)

theorem bandPeriodic_norm_le {t : Momentum} (ht : t ∈ chart) :
    ‖bandPeriodic t‖ ≤ 32 :=
  (periodicSeries_norm_le _ (normalizedFiberVector_fourier_l1 ht).1).trans
    (normalizedFiberVector_fourier_l1 ht).2

theorem bandPeriodic_apply_norm_le {t : Momentum} (ht : t ∈ chart)
    (x : Torus) : ‖bandPeriodic t x‖ ≤ 32 :=
  ((bandPeriodic t).norm_coe_le_norm x).trans (bandPeriodic_norm_le ht)

#print axioms periodicSeries_uniform
#print axioms bandPeriodic_apply_norm_le

end Maxwell.Continuum.CellBandFourier
