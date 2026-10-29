import Maxwell.Continuum.CellBandFourier
import Maxwell.Continuum.BlochUnfiber

/-! Parseval identification of the uniformly convergent vector cell
series with its actual Fourier coefficients. Haar probability corresponds
to mean square over a physical cell of side length two. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber FiberNormalization UnitAddTorus MeasureTheory
open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev torusMeasure : Measure Torus := volume

instance : IsProbabilityMeasure torusMeasure := inferInstanceAs (IsProbabilityMeasure (volume : Measure Torus))

abbrev ScalarCellL2 := Lp ℂ 2 torusMeasure
abbrev CellFieldL2 := PiLp 2 (fun _ : Fin 3 => ScalarCellL2)

def componentMap (j : Fin 3) : Polarization →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Fin 3 => ℂ) j

def componentSequence (u : FiberSpace) (j : Fin 3) : lp (fun _ : Alias => ℂ) 2 :=
  ⟨fun ν => u ν j, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using Bloch.polarization_component_summable u j)⟩

def scalarSeries (u : FiberSpace) (j : Fin 3) : C(Torus, ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℂ Torus (componentMap j) (periodicSeries u)

def scalarCellL2 (u : FiberSpace) (j : Fin 3) : ScalarCellL2 :=
  ContinuousMap.toLp 2 torusMeasure ℂ (scalarSeries u j)

def cellL2 (u : FiberSpace) : CellFieldL2 := WithLp.toLp 2 (fun j => scalarCellL2 u j)

theorem scalarSeries_hasSum (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) (j : Fin 3) :
    HasSum (fun ν => (u ν j) • mFourier ν) (scalarSeries u j) := by
  have h := (ContinuousLinearMap.compLeftContinuous ℂ Torus (componentMap j)).hasSum
    (periodicSeries_hasSum u hu)
  convert h using 1
  · ext ν x
    change (u ν j) * mFourier ν x = (mFourier ν x) * u ν j
    exact mul_comm _ _
  · rfl

theorem scalarCellL2_hasSum (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) (j : Fin 3) :
    HasSum (fun ν => (u ν j) • mFourierLp 2 ν) (scalarCellL2 u j) := by
  have h := (ContinuousMap.toLp 2 torusMeasure ℂ).hasSum (scalarSeries_hasSum u hu j)
  simpa only [scalarCellL2, torusMeasure, mFourierLp, map_smul] using h

theorem scalarCellL2_eq_fourier (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) (j : Fin 3) :
    scalarCellL2 u j = mFourierBasis.repr.symm (componentSequence u j) := by
  have h := mFourierBasis.hasSum_repr (mFourierBasis.repr.symm (componentSequence u j))
  simp only [LinearIsometryEquiv.apply_symm_apply, coe_mFourierBasis] at h
  exact (scalarCellL2_hasSum u hu j).unique h

theorem scalarCellL2_norm_sq (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) (j : Fin 3) :
    ‖scalarCellL2 u j‖ ^ 2 = ∑' ν, ‖u ν j‖ ^ 2 := by
  rw [scalarCellL2_eq_fourier u hu j, LinearIsometryEquiv.norm_map]
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (componentSequence u j)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, componentSequence] using h

theorem cellL2_norm (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) :
    ‖cellL2 u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ j : Fin 3, ‖scalarCellL2 u j‖ ^ 2) = _
  simp only [scalarCellL2_norm_sq u hu]
  rw [← Summable.tsum_finsetSum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    Bloch.polarization_component_summable u j)]
  simp only [← EuclideanSpace.norm_sq_eq]
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) u
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm

theorem scalarCellL2_ae (u : FiberSpace) (j : Fin 3) :
    scalarCellL2 u j =ᵐ[torusMeasure] fun x => periodicSeries u x j :=
  ContinuousMap.coeFn_toLp torusMeasure (scalarSeries u j)

theorem band_cellL2_norm (t : Fin 3 → ℝ) (ht : realMomentum t ∈ PeriodicBand.chart) :
    ‖cellL2 (normalizedFiberVector (realMomentum t))‖ = 1 := by
  rw [cellL2_norm _ (normalizedFiberVector_fourier_l1 ht).1, normalizedFiberVector_norm_real t ht]

#print axioms scalarCellL2_eq_fourier
#print axioms cellL2_norm
#print axioms band_cellL2_norm

end Maxwell.Continuum.CellBandFourier
