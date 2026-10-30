import Maxwell.Continuum.SourceRoutingHistoryAppend
import Maxwell.Continuum.SourceRoutingHistoryHandoff

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryHistories
open Structured Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def keys {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) : Fin 3→SortArrays.Keys q :=
  ![PhaseKeys.first colors,PhaseKeys.middle colors,PhaseKeys.last colors]

theorem targetArray_fits {q : ℕ} (p : GeometryPhase.Plan q) (target : Equiv.Perm (Port q)) :
    GeometrySort.Fits p.width (SortArrays.targetArray target) := by
  intro i
  simp only [SortArrays.targetArray,SortArrays.get_ofFn]
  exact p.coordinate_fit _

theorem keys_fit {q : ℕ} {target : Equiv.Perm (Port q)} (p : GeometryPhase.Plan q)
    (colors : RowColoring target) (slot : Fin 3) : GeometrySort.Fits p.width (keys colors slot) := by
  fin_cases slot <;> exact targetArray_fits p _

def Sequential {q : ℕ} (p : GeometryPhase.Plan q) : Prop :=
  (historyPlan p 0).following=historyPlan p 1 ∧ (historyPlan p 1).following=historyPlan p 2

theorem phase_key {q : ℕ} {target : Equiv.Perm (Port q)} (p : GeometryPhase.Plan q)
    (colors : RowColoring target) (memory : ℕ→Bool)
    (stored : GeometryArrays.Stored memory p.base p.width
      ![IncidenceEncoding.words p.width (GeometryPhase.targets target),
        IncidenceEncoding.words p.width (GeometryPhase.labels colors),
        IncidenceEncoding.words p.width (PhaseKeys.first colors),
        IncidenceEncoding.words p.width (PhaseKeys.middle colors),
        IncidenceEncoding.words p.width (PhaseKeys.last colors)]) (slot : Fin 3) :
    BitArray.Represents memory (historyPlan p slot).base p.width (IncidenceEncoding.words p.width (keys colors slot)) := by
  fin_cases slot
  · exact stored 2
  · exact stored 3
  · exact stored 4

theorem future_separated {q : ℕ} (p : GeometryHistory.Plan q) (base : ℕ) (h : p.following.base ≤ base) :
    IncidenceEncoding.Separated base (q*q*p.width) (p.slab 1) (2*q*p.stride) := by
  right
  have same : p.slab 1+2*q*p.stride=p.following.base := by
    dsimp only [GeometryHistory.Plan.slab,GeometryHistory.Plan.following];ring
  exact same ▸ h

theorem past_stored {q : ℕ} {past future : GeometryHistory.Plan q} {initial : SortArrays.Keys q}
    {before after : ℕ→Bool} (order : past.following.base ≤ future.base)
    (stored : GeometryHistory.Stored past initial (2*q) before)
    (frame : GeometryHistory.MemoryFrame future before after) :
    GeometryHistory.Stored past initial (2*q) after := by
  intro j hj
  apply frame.represents (Or.inl ?_) (stored j hj)
  have earlier:=past.slab_mono (show j+1 ≤ 2*q+1 by omega)
  have endpoint : past.slab j+q*q*past.width=past.slab (j+1) := by
    dsimp only [GeometryHistory.Plan.slab,GeometryHistory.Plan.stride];ring
  rw [endpoint]
  exact earlier.trans (order.trans (Nat.le_add_right _ _))

theorem following_base_le {q : ℕ} (p : GeometryHistory.Plan q) : p.base ≤ p.following.base :=
  Nat.le_add_right _ _

def Stored {q : ℕ} {target : Equiv.Perm (Port q)} (p : GeometryPhase.Plan q) (colors : RowColoring target)
    (memory : ℕ→Bool) : Prop := ∀slot,GeometryHistory.Stored (historyPlan p slot) (keys colors slot) (2*q) memory

#print axioms keys_fit
#print axioms past_stored
end Maxwell.Cost.RoutingPorts.Complete.GeometryHistories
