import Maxwell.Spectral.Folding
import Maxwell.Spectral.ConcreteSymmetry

/-! The exact index-four decomposition specialized to the frozen scalar
material table.  No material-symmetry or operator-binding premise remains. -/

namespace Maxwell.Spectral.Concrete

open PeriodicYee

theorem material_FCCPeriodic : Folding.FCCPeriodic material :=
  material_lattice_periodicity

theorem primitive_folding (k : Momentum) :
    (Folding.foldingMatrix k).conjTranspose *
        PeriodicYee.fiber material (Folding.conventionalMomentum k) *
        Folding.foldingMatrix k =
      sectorDiagonal (fun a => PrimitiveYee.fiber material (Folding.sectorMomentum k a)) :=
  Folding.fiber_folding material material_FCCPeriodic k

theorem primitive_folding_intertwining (k : Momentum) :
    PeriodicYee.fiber material (Folding.conventionalMomentum k) * Folding.foldingMatrix k =
      Folding.foldingMatrix k *
        sectorDiagonal (fun a => PrimitiveYee.fiber material (Folding.sectorMomentum k a)) :=
  Folding.fiber_folding_intertwining material material_FCCPeriodic k

theorem primitive_folding_unitary (k : Momentum) :
    (Folding.foldingMatrix k).conjTranspose * Folding.foldingMatrix k = 1 ∧
      Folding.foldingMatrix k * (Folding.foldingMatrix k).conjTranspose = 1 :=
  Folding.foldingMatrix_unitary k

end Maxwell.Spectral.Concrete
