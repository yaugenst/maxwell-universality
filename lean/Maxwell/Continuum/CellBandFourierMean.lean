import Maxwell.Continuum.CellBandFourierL2
import Maxwell.Continuum.CellBandFourierGauge
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The normalized torus L² norm equals one eighth of the actual physical
cell integral. The carrier has unit modulus, so the same formula holds in
the antiperiodic gauge. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber FiberNormalization MeasureTheory UnitAddTorus Set
open scoped Pointwise

theorem component_energy_integrable (u : FiberSpace) (j : Fin 3) :
    Integrable (fun x => ‖periodicSeries u x j‖ ^ 2) torusMeasure := by
  apply (((Lp.memLp (scalarCellL2 u j)).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0))).congr
  filter_upwards [scalarCellL2_ae u j] with x hx
  rw [hx]

theorem periodicSeries_mean_square (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) :
    (∫ x, ‖periodicSeries u x‖ ^ 2 ∂torusMeasure) = ‖u‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  rw [integral_finsetSum Finset.univ (fun j _ => component_energy_integrable u j)]
  have hj (j : Fin 3) : (∫ x, ‖periodicSeries u x j‖ ^ 2 ∂torusMeasure) = ‖scalarCellL2 u j‖ ^ 2 := by
    rw [Bloch.complexL2_norm_sq]
    exact integral_congr_ae ((scalarCellL2_ae u j).fun_comp (fun z : ℂ => ‖z‖ ^ 2)).symm
  simp only [hj]
  have hn := congrArg (fun r : ℝ => r ^ 2) (cellL2_norm u hu)
  rw [PiLp.norm_sq_eq_of_L2] at hn
  exact hn

def unitSpatialCell : Set Space := {x | ∀ j, x j ∈ Ioc 0 1}
def physicalCell : Set Space := (2 : ℝ) • unitSpatialCell

theorem physicalCell_mem (x : Space) : x ∈ physicalCell ↔ ∀ j, 0 < x j ∧ x j ≤ 2 := by
  rw [physicalCell, mem_smul_set_iff_inv_smul_mem₀ (by norm_num : (2 : ℝ) ≠ 0)]
  change (∀ j, 0 < (2 : ℝ)⁻¹ * x j ∧ (2 : ℝ)⁻¹ * x j ≤ 1) ↔ _
  constructor <;> intro h j <;> have hj := h j <;> constructor <;> linarith

theorem periodicSeries_integral_unitSpatialCell (u : FiberSpace) :
    (∫ x, ‖periodicSeries u x‖ ^ 2 ∂torusMeasure) =
      ∫ x in unitSpatialCell, ‖antiperiodicField u ((2 : ℝ) • x)‖ ^ 2 := by
  have ht := integral_preimage (fun x : Torus => ‖periodicSeries u x‖ ^ 2)
    (fun _ : Fin 3 => (0 : ℝ))
  have he : MeasurableEmbedding (@WithLp.ofLp 2 (Fin 3 → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
  have hp := (PiLp.volume_preserving_ofLp (Fin 3)).restrict_preimage_emb he
    {x : Fin 3 → ℝ | ∀ j, x j ∈ Ioc 0 1}
  have hi := hp.integral_comp he
    (fun x : Fin 3 → ℝ => ‖periodicSeries u (fun j => (x j : UnitAddCircle))‖ ^ 2)
  have hpoint (x : Space) : torusPoint ((2 : ℝ) • x) = fun j => (x j : UnitAddCircle) := by
    funext j
    change (((2 * x j) / 2 : ℝ) : UnitAddCircle) = (x j : UnitAddCircle)
    congr 1
    ring
  simp only [zero_add] at ht
  change (∫ x, ‖periodicSeries u x‖ ^ 2 ∂torusMeasure) = _ at ht
  rw [ht, ← hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change ‖periodicSeries u (fun j => (x j : UnitAddCircle))‖ ^ 2 =
      ‖antiperiodicField u ((2 : ℝ) • x)‖ ^ 2
    rw [antiperiodicField_norm, hpoint]

theorem physical_mean_square (u : FiberSpace) (hu : Summable (fun ν => ‖u ν‖)) :
    (1 / 8 : ℝ) * (∫ x in physicalCell, ‖antiperiodicField u x‖ ^ 2) = ‖u‖ ^ 2 := by
  have hscale := Measure.setIntegral_comp_smul_of_pos (volume : Measure Space)
    (fun x => ‖antiperiodicField u x‖ ^ 2) unitSpatialCell (by norm_num : (0 : ℝ) < 2)
  have hdim : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  rw [hdim] at hscale
  change (∫ x in unitSpatialCell, ‖antiperiodicField u ((2 : ℝ) • x)‖ ^ 2) =
    ((2 : ℝ) ^ 3)⁻¹ * (∫ x in physicalCell, ‖antiperiodicField u x‖ ^ 2) at hscale
  norm_num only at hscale
  rw [← periodicSeries_mean_square u hu, periodicSeries_integral_unitSpatialCell, hscale]

theorem band_physical_mean_square (t : Fin 3 → ℝ) (ht : realMomentum t ∈ PeriodicBand.chart) :
    (1 / 8 : ℝ) *
      (∫ x in physicalCell, ‖antiperiodicField (normalizedFiberVector (realMomentum t)) x‖ ^ 2) = 1 := by
  rw [physical_mean_square _ (normalizedFiberVector_fourier_l1 ht).1,
    normalizedFiberVector_norm_real t ht, one_pow]

#print axioms physical_mean_square
#print axioms band_physical_mean_square

end Maxwell.Continuum.CellBandFourier
