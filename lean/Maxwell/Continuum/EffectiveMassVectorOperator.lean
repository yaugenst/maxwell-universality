import Maxwell.Continuum.EffectiveMassMultiplierMeasurable
import Maxwell.Continuum.VectorMultiplier
import Maxwell.Continuum.OperatorSandwichError

/-! Actual rectangular L² multiplication operators for the two complete
Fourier-vector multipliers, and their quantitative operator comparison. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber Auxiliary
open scoped InnerProduct

abbrev MomentumFiberL2 := Lp FiberSpace 2 (volume : Measure Space)

def bandVectorData {h z : ℝ} (D : Calibration h z) :
    VectorMultiplier.Data (H := FiberSpace) (volume : Measure Space) 4 where
  coefficient := vectorMultiplier h z
  measurable := vectorMultiplier_measurable D
  nonneg := by norm_num
  bound := vectorMultiplier_norm_le D

def referenceVectorData :
    VectorMultiplier.Data (H := FiberSpace) (volume : Measure Space) 2 where
  coefficient := referenceVectorMultiplier
  measurable := referenceVectorMultiplier_continuous.aestronglyMeasurable
  nonneg := by norm_num
  bound := referenceVectorMultiplier_norm_le

def bandVectorOperator {h z : ℝ} (D : Calibration h z) : ScalarL2 →L[ℂ] MomentumFiberL2 :=
  (bandVectorData D).operator

def referenceVectorOperator : ScalarL2 →L[ℂ] MomentumFiberL2 := referenceVectorData.operator

theorem bandVectorOperator_ae {h z : ℝ} (D : Calibration h z) (f : ScalarL2) :
    bandVectorOperator D f =ᵐ[volume] fun p => f p • vectorMultiplier h z p :=
  (bandVectorData D).operator_ae f

theorem referenceVectorOperator_ae (f : ScalarL2) :
    referenceVectorOperator f =ᵐ[volume] fun p => f p • referenceVectorMultiplier p :=
  referenceVectorData.operator_ae f

theorem bandVectorOperator_norm {h z : ℝ} (D : Calibration h z) :
    ‖bandVectorOperator D‖ ≤ 4 := (bandVectorData D).operator_norm_le

theorem referenceVectorOperator_norm : ‖referenceVectorOperator‖ ≤ 2 :=
  referenceVectorData.operator_norm_le

theorem vectorOperator_error {h z : ℝ} (D : Calibration h z) :
    ‖bandVectorOperator D - referenceVectorOperator‖ ≤ (2 : ℝ)^130 * h := by
  have hh := D.h_pos
  exact (bandVectorData D).operator_difference_norm referenceVectorData (by positivity)
    (vectorMultiplier_error D)

theorem diagonalOperator_error {h z : ℝ} (D : Calibration h z)
    (W : MomentumFiberL2 →L[ℂ] MomentumFiberL2) (hW : ‖W‖ ≤ 1) :
    ‖(bandVectorOperator D)†.comp (W.comp (bandVectorOperator D)) -
      referenceVectorOperator†.comp (W.comp referenceVectorOperator)‖ ≤ (2 : ℝ)^133 * h := by
  have hh := D.h_pos
  have hv := vectorOperator_error D
  have ha := bandVectorOperator_norm D
  have hb := referenceVectorOperator_norm
  calc
    _ ≤ ‖bandVectorOperator D - referenceVectorOperator‖ * ‖W‖ *
        (‖bandVectorOperator D‖ + ‖referenceVectorOperator‖) :=
      OperatorPerturbation.sandwich_difference_norm _ _ W
    _ ≤ ((2 : ℝ)^130 * h) * 1 * (4 + 2) :=
      mul_le_mul (mul_le_mul hv hW (norm_nonneg _) (by positivity)) (add_le_add ha hb)
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ ≤ (2 : ℝ)^133 * h := by nlinarith

end Maxwell.Continuum.EffectiveMass
