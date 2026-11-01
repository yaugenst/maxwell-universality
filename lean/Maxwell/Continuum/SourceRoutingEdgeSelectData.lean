import Maxwell.Continuum.SourceRoutingOriginalSelect
import Maxwell.Continuum.SourceRoutingPhaseData

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def edgeSelectProgram : Control := .divide 1230 1200 1232 1233
  (Control.prepend [.multiply 1220 1232,.multiply 1200 1232,.add 1233 1232] .done)
def edgeSelectValues {q : ℕ} (p : GeometrySort.Plan q) (round old edge : ℕ) : ℕ→ℕ :=
  edgeSelectProgram.evaluate (Function.update (GeometrySort.seed p round old) 1230 edge)
def edgeSelectCleanup : List NatAssign.Instruction :=
  [.copy 1231 1201,.literal 1230 0,.literal 1231 0,.literal 1232 0,.literal 1233 0]
def edgeSelectCode : Code := .seq (loadCode 1257 1230)
  (.seq edgeSelectProgram.code (.seq (BankArray.readCanonicalCode 711 1232 1260 718 1231)
    (NatAssign.code edgeSelectCleanup)))

theorem edgeSelect_valid : edgeSelectProgram.Valid := by
  simp [edgeSelectProgram,Control.Valid,Control.prepend,NatAssign.Instruction.Valid,controls]

theorem edgeSelect_other {q : ℕ} (p : GeometrySort.Plan q) (round old edge j : ℕ)
    (h30 : j≠1230) (h32 : j≠1232) (h33 : j≠1233) :
    edgeSelectValues p round old edge j=GeometrySort.seed p round old j := by
  change edgeSelectProgram.evaluate _ j=_
  rw [edgeSelectProgram.evaluate_other _ j (by
    simp [edgeSelectProgram,Control.writes,Control.prepend,NatAssign.Instruction.target,h32,h33])]
  exact Function.update_of_ne h30 _ _

theorem edgeSelect_index {half : ℕ} (p : GeometrySort.Plan (2*half)) (round old : ℕ)
    (edge : Fin (half*(2*half))) :
    edgeSelectValues p round old edge.val 1232=
      (finProdFinEquiv (Gluing.pairPort (finProdFinEquiv.symm edge) false)).val := by
  simp [edgeSelectValues,edgeSelectProgram,Control.evaluate,Control.prepend,divided,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
    GeometrySort.seed,Gluing.pairPort,finProdFinEquiv]

theorem inverse_incidence {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (edge : E) (side : Bool) :
    (GeometryPhase.targets data.target.symm).get (finProdFinEquiv (Gluing.pairPort (data.pair edge) side))=
      (finProdFinEquiv (Gluing.token data (edge,side))).val := by
  simp only [GeometryPhase.targets,GeometryPhase.port,SortArrays.get_ofFn,Equiv.symm_apply_apply]
  rw [←data.target_incidence edge side,Equiv.symm_apply_apply]
  rfl

theorem edgeSelect_cleaned {q : ℕ} (p : GeometrySort.Plan q) (round old edge index : ℕ) :
    NatAssign.values edgeSelectCleanup (Function.update (edgeSelectValues p round old edge) 1231 index)=
      GeometrySort.seed p round index := by
  funext j
  by_cases h1 : j=1201
  · subst j
    simp [edgeSelectCleanup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  by_cases h30 : j=1230
  · subst j
    simp [edgeSelectCleanup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  by_cases h31 : j=1231
  · subst j
    simp [edgeSelectCleanup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  by_cases h32 : j=1232
  · subst j
    simp [edgeSelectCleanup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  by_cases h33 : j=1233
  · subst j
    simp [edgeSelectCleanup,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
  simp only [edgeSelectCleanup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,Function.update_of_ne h1,Function.update_of_ne h30,
    Function.update_of_ne h31,Function.update_of_ne h32,Function.update_of_ne h33,
    edgeSelect_other p round old edge j h30 h32 h33]
  simp only [GeometrySort.seed,h1,ite_false]

#print axioms edgeSelect_cleaned
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
