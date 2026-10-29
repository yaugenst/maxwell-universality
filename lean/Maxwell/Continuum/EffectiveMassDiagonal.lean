import Maxwell.Continuum.AngularWell
import Maxwell.Continuum.EffectiveMassVectorOperator

/-! The actual diagonal-alias effective-mass comparison, with the
literal unitary Fourier conjugate of multiplication by w. -/

noncomputable section

namespace Maxwell.Continuum.EffectiveMass

open FreeFiber Auxiliary
open scoped InnerProduct

def diagonalBandOperator {h z : ℝ} (D : Calibration h z) : ScalarL2 →L[ℂ] ScalarL2 :=
  (bandVectorOperator D)†.comp ((angularWellConvolution FiberSpace).comp (bandVectorOperator D))

def diagonalReferenceOperator : ScalarL2 →L[ℂ] ScalarL2 :=
  referenceVectorOperator†.comp ((angularWellConvolution FiberSpace).comp referenceVectorOperator)

theorem diagonalComparison_error {h z : ℝ} (D : Calibration h z) :
    ‖diagonalBandOperator D - diagonalReferenceOperator‖ ≤ (2 : ℝ)^133 * h :=
  diagonalOperator_error D (angularWellConvolution FiberSpace) (angularWellConvolution_norm FiberSpace)

end Maxwell.Continuum.EffectiveMass
