import Maxwell.Certificate.PointWitness.Vector
import Maxwell.Spectral.ResidualCertificate
import Mathlib.Analysis.Matrix.Hermitian

namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
noncomputable section

def pointFiber : Matrix Electric Electric ℂ :=
  PrimitiveYee.fiber Concrete.material (timeReversalMomentum ![1,1,0])

def pointOperator : EuclideanSpace ℂ Electric →ₗ[ℂ] EuclideanSpace ℂ Electric :=
  pointFiber.toEuclideanLin

theorem pointOperator_symmetric : pointOperator.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (PrimitiveYee.fiber_hermitian _ _)

end
end Maxwell.Certificate.PointWitness
