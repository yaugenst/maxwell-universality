import Maxwell.Continuum.SourceRoutingHistoriesLayout

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryHistories
set_option maxRecDepth 16384

def MemoryFrame {q : ℕ} (p : GeometryPhase.Plan q) (before after : ℕ→Bool) : Prop :=
  ∀address,(∀slot : Fin 3,address<(historyPlan p slot).slab 1 ∨
    (historyPlan p slot).slab 1+2*q*(historyPlan p slot).stride ≤ address)→after address=before address

theorem MemoryFrame.refl {q : ℕ} (p : GeometryPhase.Plan q) (memory : ℕ→Bool) :
    MemoryFrame p memory memory := fun _ _ => rfl

theorem MemoryFrame.trans {q : ℕ} {p : GeometryPhase.Plan q} {a b c : ℕ→Bool}
    (first : MemoryFrame p a b) (second : MemoryFrame p b c) : MemoryFrame p a c :=
  fun address outside => (second address outside).trans (first address outside)

theorem MemoryFrame.of_eq {q : ℕ} (p : GeometryPhase.Plan q) {before after : ℕ→Bool}
    (same : after=before) : MemoryFrame p before after := by subst after;exact .refl _ _

theorem MemoryFrame.of_history {q : ℕ} (p : GeometryPhase.Plan q) (slot : Fin 3) {before after : ℕ→Bool}
    (frame : GeometryHistory.MemoryFrame (historyPlan p slot) before after) : MemoryFrame p before after :=
  fun address outside => frame address (outside slot)

#print axioms MemoryFrame.of_history
end Maxwell.Cost.RoutingPorts.Complete.GeometryHistories
