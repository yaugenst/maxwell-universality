import Maxwell.Continuum.BandWavePacketPhysical
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact angular-momentum measures for the scaled Bloch packet. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Bloch
open scoped ENNReal

def angularDensity : ℝ := ((2 * Real.pi)^3)⁻¹
def angularMeasure : Measure Space := ENNReal.ofReal angularDensity • volume

theorem angularDensity_pos : 0 < angularDensity := by unfold angularDensity; positivity

def dilation (h : ℝ) (hh : 0 < h) : Space ≃ᵐ Space where
  toFun x := h • x
  invFun x := h⁻¹ • x
  left_inv x := by dsimp only; rw [smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  right_inv x := by dsimp only; rw [smul_smul, mul_inv_cancel₀ hh.ne', one_smul]
  measurable_toFun := measurable_const_smul h
  measurable_invFun := measurable_const_smul h⁻¹

def scaledDensity (h : ℝ) : ℝ := angularDensity * h^3

theorem scaledDensity_pos {h : ℝ} (hh : 0 < h) : 0 < scaledDensity h :=
  mul_pos angularDensity_pos (pow_pos hh _)

theorem inverseDilation_map {h : ℝ} (hh : 0 < h) :
    angularMeasure.map (dilation h hh).symm = ENNReal.ofReal (scaledDensity h) • volume := by
  rw [angularMeasure, Measure.map_smul _ (dilation h hh).symm.measurable.aemeasurable]
  have hm := Measure.map_addHaar_smul (volume : Measure Space) (inv_ne_zero hh.ne')
  change Measure.map (fun x : Space => h⁻¹ • x) volume = _ at hm
  change ENNReal.ofReal angularDensity • Measure.map (fun x : Space => h⁻¹ • x) volume = _
  rw [hm]
  simp only [show Module.finrank ℝ Space = 3 from finrank_euclideanSpace_fin,
    inv_pow, inv_inv, abs_of_pos (pow_pos hh 3), smul_smul]
  rw [← ENNReal.ofReal_mul angularDensity_pos.le]
  rfl

theorem inverseDilation_measurePreserving {h : ℝ} (hh : 0 < h) :
    MeasurePreserving (dilation h hh).symm angularMeasure
      (ENNReal.ofReal (scaledDensity h) • (volume : Measure Space)) where
  measurable := (dilation h hh).symm.measurable
  map_eq := inverseDilation_map hh

theorem quasi_coe_measurePreserving :
    MeasurePreserving (Subtype.val : QuasiCell → Space) quasiMeasure
      (angularMeasure.restrict quasiCell) where
  measurable := measurable_subtype_coe
  map_eq := by
    rw [quasiMeasure, Measure.map_smul _ measurable_subtype_coe.aemeasurable,
      map_comap_subtype_coe quasiCell_measurable, angularMeasure, Measure.restrict_smul]
    rfl

def amplitudeFactor (h : ℝ) : ℝ := (Real.sqrt (scaledDensity h))⁻¹

theorem amplitudeFactor_pos {h : ℝ} (hh : 0 < h) : 0 < amplitudeFactor h :=
  inv_pos.mpr (Real.sqrt_pos.2 (scaledDensity_pos hh))

theorem amplitudeFactor_square {h : ℝ} (hh : 0 < h) :
    amplitudeFactor h ^ 2 * scaledDensity h = 1 := by
  rw [amplitudeFactor, inv_pow, Real.sq_sqrt (scaledDensity_pos hh).le,
    inv_mul_cancel₀ (scaledDensity_pos hh).ne']

#print axioms inverseDilation_measurePreserving
#print axioms quasi_coe_measurePreserving
#print axioms amplitudeFactor_square

end Maxwell.Continuum.EffectiveMass
