import Maxwell.Continuum.BlochL2
import Maxwell.Continuum.FreeFiber
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The period-two Fourier coordinate has half the unit-cell spacing.
The Jacobian is 1/8 in three dimensions, and the alias momentum is exactly
2π times the Fourier coordinate used by the Plancherel transform. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

def half : Space ≃ᵐ Space where
  toFun x := (1 / 2 : ℝ) • x
  invFun x := (2 : ℝ) • x
  left_inv x := by simp only [smul_smul]; norm_num
  right_inv x := by simp only [smul_smul]; norm_num
  measurable_toFun := measurable_const_smul (1 / 2 : ℝ)
  measurable_invFun := measurable_const_smul (2 : ℝ)

theorem half_map_volume : (volume : Measure Space).map half = (8 : ENNReal) • volume := by
  change Measure.map (fun x : Space => (1 / 2 : ℝ) • x) volume = _
  have h := Measure.map_addHaar_smul (volume : Measure Space) (by norm_num : (1 / 2 : ℝ) ≠ 0)
  simpa only [show Module.finrank ℝ Space = 3 from finrank_euclideanSpace_fin,
    show |((1 / 2 : ℝ) ^ 3)⁻¹| = 8 by norm_num, ENNReal.ofReal_ofNat] using h

theorem half_measurePreserving :
    MeasurePreserving half ((1 / 8 : ENNReal) • (volume : Measure Space)) volume where
  measurable := half.measurable
  map_eq := by
    rw [Measure.map_smul _ half.measurable.aemeasurable, half_map_volume, smul_smul]
    rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_smul]

/-- The source-cell measure includes the exact Jacobian of ξ=(r+ν)/2. -/
def normalizedCellMeasure : Measure Cell := (1 / 8 : ENNReal) • cellMeasure

def frequencyJoin : Cell × Alias ≃ᵐ Space := join.trans half

theorem frequencyJoin_measurePreserving :
    MeasurePreserving frequencyJoin (normalizedCellMeasure.prod Measure.count) volume := by
  have h := half_measurePreserving.comp (join_measurePreserving.smul_measure (1 / 8 : ENNReal))
  simpa only [normalizedCellMeasure, Measure.prod_smul_left, frequencyJoin,
    MeasurableEquiv.coe_trans] using h

@[simp] theorem frequencyJoin_apply (r : Cell) (n : Alias) (i : Fin 3) :
    frequencyJoin (r, n) i = ((r : Space) i + (n i : ℝ)) / 2 := by
  change ((1 / 2 : ℝ) • (integerVector n + (r : Space))) i = _
  change (1 / 2 : ℝ) * ((n i : ℝ) + (r : Space) i) = _
  ring

def quasimomentum (r : Cell) : Space :=
  WithLp.toLp 2 (fun i => Real.pi * (r : Space) i - Real.pi / 2)

def realFiberMomentum (r : Cell) : FreeFiber.Momentum :=
  fun i => (quasimomentum r i : ℂ)

theorem quasimomentum_mem (r : Cell) (i : Fin 3) :
    -Real.pi / 2 ≤ quasimomentum r i ∧ quasimomentum r i < Real.pi / 2 := by
  have h := r.property i
  change -Real.pi / 2 ≤ Real.pi * (r : Space) i - Real.pi / 2 ∧
    Real.pi * (r : Space) i - Real.pi / 2 < Real.pi / 2
  constructor <;> nlinarith [Real.pi_pos]

/-- The Fourier derivative normalization agrees exactly with the momenta
of the actual maximal free fibers, including the antiperiodic corner. -/
theorem frequencyJoin_aliasMomentum (r : Cell) (n : Alias) (i : Fin 3) :
    (2 * Real.pi : ℂ) * (frequencyJoin (r, n) i : ℂ) =
      FreeFiber.aliasMomentum (realFiberMomentum r) n i := by
  rw [frequencyJoin_apply]
  change (2 * Real.pi : ℂ) * ((((r : Space) i + (n i : ℝ)) / 2 : ℝ) : ℂ) =
    (Real.pi : ℂ) / 2 + ((Real.pi * (r : Space) i - Real.pi / 2 : ℝ) : ℂ) +
      (Real.pi : ℂ) * (n i : ℂ)
  push_cast
  ring

abbrev NormalizedCellAliasL2 :=
  Lp ℂ 2 (normalizedCellMeasure.prod (Measure.count : Measure Alias))
abbrev NormalizedCellAliasFieldL2 := PiLp 2 (fun _ : Fin 3 => NormalizedCellAliasL2)

def normalizedRegroup : ScalarL2 ≃ₗᵢ[ℂ] NormalizedCellAliasL2 :=
  measureEquivL2 frequencyJoin frequencyJoin_measurePreserving

/-- The physical period-two Fourier regrouping, with its exact source measure. -/
def transform : FieldL2 ≃ₗᵢ[ℂ] NormalizedCellAliasFieldL2 :=
  fieldFourier.trans
    (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 3 => normalizedRegroup))

theorem transform_norm (u : FieldL2) : ‖transform u‖ = ‖u‖ := transform.norm_map u

theorem transform_inner (u v : FieldL2) :
    inner ℂ (transform u) (transform v) = inner ℂ u v := transform.inner_map_map u v

theorem transform_ae (u : FieldL2) (i : Fin 3) :
    transform u i =ᵐ[normalizedCellMeasure.prod Measure.count]
      (fun rn => fieldFourier u i (frequencyJoin rn)) :=
  measureEquivL2_ae frequencyJoin frequencyJoin_measurePreserving (fieldFourier u i)

end Maxwell.Continuum.Bloch
