import Maxwell.Certificate.GlobalPhaseBank.Positive
import Maxwell.Certificate.GlobalComputedMaterial
import Maxwell.Spectral.LocalClusterCount

namespace Maxwell.Certificate.GlobalInputs
open DyadicKernel FourierBinding Maxwell.Spectral
noncomputable section

def centerAction (i : Fin 2056) (raw : Action.VectorField) : Action.Result :=
  Action.compute (GlobalPhaseBank.centerSymbols i) (GlobalComputedMaterial.field 157) raw

def negativeAction (i : Fin 604) (raw : Action.VectorField) : Action.Result :=
  Action.compute (GlobalPhaseBank.negativeSymbols i) (GlobalComputedMaterial.field 0) raw

def uniformAction (raw : Action.VectorField) : Action.Result :=
  Action.compute GlobalPhaseBank.uniformSymbols (GlobalComputedMaterial.field 448) raw

theorem material_local : GlobalComputedMaterial.material 448 = LocalClusterCount.localMaterial := by
  ext r
  norm_num [GlobalComputedMaterial.material,LocalClusterCount.localMaterial]

theorem centerAction_contains (i : Fin 2056) (raw : Action.VectorField) :
    (centerAction i raw).Contains GlobalComparison.comparatorMaterial (FrozenGlobal.center i) raw := by
  rw [← GlobalComputedMaterial.material_comparator]
  exact Action.compute_contains _ _ _ _ _
    (GlobalPhaseBank.centerSymbols_projectionValid i)
    (GlobalComputedMaterial.materialValid 157 (by norm_num))
    (GlobalPhaseBank.centerSymbols_contains i) (GlobalComputedMaterial.field_contains 157)

theorem negativeAction_contains (i : Fin 604) (raw : Action.VectorField) :
    (negativeAction i raw).Contains Concrete.baseMaterial (FrozenNegative.center i) raw := by
  rw [← GlobalComputedMaterial.material_base]
  exact Action.compute_contains _ _ _ _ _
    (GlobalPhaseBank.negativeSymbols_projectionValid i)
    (GlobalComputedMaterial.materialValid 0 (by norm_num))
    (GlobalPhaseBank.negativeSymbols_contains i) (GlobalComputedMaterial.field_contains 0)

theorem uniformAction_contains (raw : Action.VectorField) :
    (uniformAction raw).Contains LocalClusterCount.localMaterial (fun _ => 1/2) raw := by
  rw [← material_local]
  exact Action.compute_contains _ _ _ _ _
    GlobalPhaseBank.uniformSymbols_projectionValid
    (GlobalComputedMaterial.materialValid 448 (by norm_num))
    GlobalPhaseBank.uniformSymbols_contains (GlobalComputedMaterial.field_contains 448)

theorem center_projected_transverse (i : Fin 2056) (raw : Action.VectorField) :
    GlobalCenter.projectedField 52 (FrozenGlobal.center i) (Action.toRectField raw) ∈
      transverseSubspace (FrozenGlobal.center i) :=
  Action.projectedField_transverse _ _ _
    (GlobalPhaseBank.centerSymbols_projectionValid i) (GlobalPhaseBank.centerSymbols_contains i)

theorem negative_projected_transverse (i : Fin 604) (raw : Action.VectorField) :
    GlobalCenter.projectedField 52 (FrozenNegative.center i) (Action.toRectField raw) ∈
      transverseSubspace (FrozenNegative.center i) :=
  Action.projectedField_transverse _ _ _
    (GlobalPhaseBank.negativeSymbols_projectionValid i) (GlobalPhaseBank.negativeSymbols_contains i)

theorem uniform_projected_transverse (raw : Action.VectorField) :
    GlobalCenter.projectedField 52 (fun _ => 1/2) (Action.toRectField raw) ∈
      transverseSubspace (fun _ => 1/2) :=
  Action.projectedField_transverse _ _ _
    GlobalPhaseBank.uniformSymbols_projectionValid GlobalPhaseBank.uniformSymbols_contains

end
end Maxwell.Certificate.GlobalInputs
