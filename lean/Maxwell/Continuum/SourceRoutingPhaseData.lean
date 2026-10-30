import Maxwell.Continuum.SourceRoutingScatterArray
import Maxwell.Continuum.SourceRoutingGeometryArrays

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
open Maxwell.Logical.Routing
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

def port {q : ℕ} (i : Fin (q*q)) : Port q := finProdFinEquiv.symm i
def labels {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) : Vector ℕ (q*q) :=
  Vector.ofFn (fun i => q*(colors.color (port i)).val)
def targets {q : ℕ} (target : Equiv.Perm (Port q)) : Vector ℕ (q*q) :=
  Vector.ofFn (fun i => (finProdFinEquiv (target (port i))).val)
def firstValue {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) (i : Fin (q*q)) : ℕ :=
  (colors.color (port i)).val
def middleAddress {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) (i : Fin (q*q)) : Fin (q*q) :=
  PhaseKeys.middleAddress colors (port i)
def lastAddress {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) (i : Fin (q*q)) : Fin (q*q) :=
  PhaseKeys.lastAddress colors (port i)
def middleValue {q : ℕ} (target : Equiv.Perm (Port q)) (i : Fin (q*q)) : ℕ := (target (port i)).2.val
def lastValue {q : ℕ} (target : Equiv.Perm (Port q)) (i : Fin (q*q)) : ℕ := (target (port i)).1.val

def arrays {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) (width : ℕ)
    (initial : Fin 3→Vector (List Bool) (q*q)) (k : ℕ) (hk : k ≤ q*q) : Fin 5→Vector (List Bool) (q*q) :=
  ![IncidenceEncoding.words width (targets target),IncidenceEncoding.words width (labels colors),
    GeometryScatter.run id (firstValue colors) width (initial 0) k hk,
    GeometryScatter.run (middleAddress colors) (middleValue target) width (initial 1) k hk,
    GeometryScatter.run (lastAddress colors) (lastValue target) width (initial 2) k hk]

def updateArrays {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) (width : ℕ)
    (saved : Fin 5→Vector (List Bool) (q*q)) (i : Fin (q*q)) : Fin 5→Vector (List Bool) (q*q) :=
  Function.update (Function.update (Function.update saved 2
    ((saved 2).set i (IncidenceEncoding.word width (firstValue colors i)))) 3
      ((saved 3).set (middleAddress colors i) (IncidenceEncoding.word width (middleValue target i)))) 4
        ((saved 4).set (lastAddress colors i) (IncidenceEncoding.word width (lastValue target i)))

theorem arrays_succ {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) (width : ℕ)
    (initial : Fin 3→Vector (List Bool) (q*q)) (k : ℕ) (hk : k+1 ≤ q*q) :
    arrays colors width initial (k+1) hk=
      updateArrays colors width (arrays colors width initial k (by omega)) ⟨k,by omega⟩ := by
  funext slot
  fin_cases slot <;> simp [arrays,updateArrays,GeometryScatter.run_succ]

theorem arrays_complete {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) (width : ℕ)
    (initial : Fin 3→Vector (List Bool) (q*q)) :
    arrays colors width initial (q*q) le_rfl=
      ![IncidenceEncoding.words width (targets target),IncidenceEncoding.words width (labels colors),
        IncidenceEncoding.words width (PhaseKeys.first colors),
        IncidenceEncoding.words width (PhaseKeys.middle colors),
        IncidenceEncoding.words width (PhaseKeys.last colors)] := by
  have first := GeometryScatter.run_complete id Function.injective_id (firstValue colors)
    width (initial 0) (PhaseKeys.first colors) (fun i => by
      have h:=PhaseKeys.first_at colors (port i)
      simpa only [port,firstValue,id_eq,Equiv.apply_symm_apply] using h)
  have middle := GeometryScatter.run_complete (middleAddress colors)
    ((PhaseKeys.middleAddress_injective colors).comp finProdFinEquiv.symm.injective)
    (middleValue target) width (initial 1) (PhaseKeys.middle colors) (fun i => PhaseKeys.middle_at colors (port i))
  have last := GeometryScatter.run_complete (lastAddress colors)
    ((PhaseKeys.lastAddress_injective colors).comp finProdFinEquiv.symm.injective)
    (lastValue target) width (initial 2) (PhaseKeys.last colors) (fun i => PhaseKeys.last_at colors (port i))
  simp only [arrays,first,middle,last]

#print axioms arrays_complete
end Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
