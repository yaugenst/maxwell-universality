import Maxwell.Certificate.GlobalInputs
import Maxwell.Certificate.GlobalDerivativeActionSound

namespace Maxwell.Certificate.GlobalInputs
open DyadicKernel FourierBinding Maxwell.Spectral
noncomputable section

def centerDerivative (i : Fin 2056) (axis : Fin 3) (raw : Action.VectorField) : DerivativeAction.Result :=
  DerivativeAction.compute axis (GlobalPhaseBank.centerSymbols i) (GlobalComputedMaterial.field 157)
    (centerAction i raw).projected (centerAction i raw).weighted

def negativeDerivative (i : Fin 604) (axis : Fin 3) (raw : Action.VectorField) : DerivativeAction.Result :=
  DerivativeAction.compute axis (GlobalPhaseBank.negativeSymbols i) (GlobalComputedMaterial.field 0)
    (negativeAction i raw).projected (negativeAction i raw).weighted

def uniformDerivative (axis : Fin 3) (raw : Action.VectorField) : DerivativeAction.Result :=
  DerivativeAction.compute axis GlobalPhaseBank.uniformSymbols (GlobalComputedMaterial.field 448)
    (uniformAction raw).projected (uniformAction raw).weighted

theorem centerDerivative_contains (i : Fin 2056) (axis : Fin 3) (raw : Action.VectorField) :
    (centerDerivative i axis raw).Contains GlobalComparison.comparatorMaterial
      (FrozenGlobal.center i) axis
      (GlobalCenter.projectedField 52 (FrozenGlobal.center i) (Action.toRectField raw)) := by
  have hc := centerAction_contains i raw
  apply DerivativeAction.compute_contains _ _ _ _ _ _ _ _
    (GlobalPhaseBank.centerSymbols_projectionValid i)
    (GlobalComputedMaterial.materialValid 157 (by norm_num))
    (GlobalPhaseBank.centerSymbols_contains i) _ hc.1 hc.2.2.1
  simpa only [Action.toRectField,GlobalComputedMaterial.material_comparator] using GlobalComputedMaterial.field_contains 157

theorem negativeDerivative_contains (i : Fin 604) (axis : Fin 3) (raw : Action.VectorField) :
    (negativeDerivative i axis raw).Contains Concrete.baseMaterial
      (FrozenNegative.center i) axis
      (GlobalCenter.projectedField 52 (FrozenNegative.center i) (Action.toRectField raw)) := by
  have hc := negativeAction_contains i raw
  apply DerivativeAction.compute_contains _ _ _ _ _ _ _ _
    (GlobalPhaseBank.negativeSymbols_projectionValid i)
    (GlobalComputedMaterial.materialValid 0 (by norm_num))
    (GlobalPhaseBank.negativeSymbols_contains i) _ hc.1 hc.2.2.1
  simpa only [Action.toRectField,GlobalComputedMaterial.material_base] using GlobalComputedMaterial.field_contains 0

theorem uniformDerivative_contains (axis : Fin 3) (raw : Action.VectorField) :
    (uniformDerivative axis raw).Contains LocalClusterCount.localMaterial (fun _ => 1/2) axis
      (GlobalCenter.projectedField 52 (fun _ => 1/2) (Action.toRectField raw)) := by
  have hc := uniformAction_contains raw
  apply DerivativeAction.compute_contains _ _ _ _ _ _ _ _
    GlobalPhaseBank.uniformSymbols_projectionValid
    (GlobalComputedMaterial.materialValid 448 (by norm_num))
    GlobalPhaseBank.uniformSymbols_contains _ hc.1 hc.2.2.1
  simpa only [Action.toRectField,material_local] using GlobalComputedMaterial.field_contains 448

end
end Maxwell.Certificate.GlobalInputs
