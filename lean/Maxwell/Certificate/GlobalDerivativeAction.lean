import Maxwell.Certificate.DyadicKernelAction
import Maxwell.Certificate.GlobalDerivativeKernel

namespace Maxwell.Certificate.DyadicKernel.DerivativeAction
open Action
noncomputable section

def theta : Rectangle := ⟨0,1414847550405688,1⟩
def projectorScale : Rectangle := ⟨140737488355328,0,0⟩

def symbols (axis : Fin 3) (d : VectorField) : VectorField :=
  VectorField.build fun r => Derivative.axisRound 52 axis theta (d.get r)

def materialApply (material field : VectorField) : VectorField :=
  forward (divideMaterial (inverse field) material)

def projectionPrime (d dp field : VectorField) : VectorField :=
  VectorField.build fun r =>
    (Derivative.projectionPrimeRound 52 (d.get r) (dp.get r) (field.get r)
      (laplacianRound 52 (d.get r))).getD zeroTriple

structure Result where
  curl : VectorField
  weighted : VectorField
  magnetic : VectorField
  projection : VectorField
  auxiliary : VectorField

def compute (axis : Fin 3) (d material field weighted : VectorField) : Result :=
  let dp := symbols axis d
  let curl := adjointCurl dp field
  let wp := materialApply material curl
  let magnetic := VectorField.build fun r => Derivative.magneticPrimeRound 52
    (d.get r) (dp.get r) (weighted.get r) (wp.get r)
  let projection := projectionPrime d dp field
  let auxiliary := VectorField.build fun r => Derivative.scaledAddRound 52
    (magnetic.get r) projectorScale (projection.get r)
  ⟨curl,wp,magnetic,projection,auxiliary⟩

end
end Maxwell.Certificate.DyadicKernel.DerivativeAction
