import Maxwell.Cost.DoublingPass.Loop

namespace Maxwell.Cost.DoublingPass
open Maxwell.Logical.Routing

def Layout.flip (layout : Layout) : Layout :=
  ⟨layout.width,layout.newJump,layout.newMinimum,layout.oldJump,layout.oldMinimum⟩

@[simp] theorem Layout.flip_flip (layout : Layout) : layout.flip.flip = layout := by cases layout; rfl

/-- Both pairs are disjoint because they alternate as writable output arrays. -/
structure Layout.PingPong (layout : Layout) (n : ℕ) : Prop where
  forward : layout.Separated n
  backward : layout.flip.Separated n

theorem Layout.PingPong.flip {layout : Layout} {n : ℕ} (h : layout.PingPong n) :
    layout.flip.PingPong n := ⟨h.backward,by simpa using h.forward⟩

theorem Represents.flip {layout : Layout} {n : ℕ} {memory : ℕ → Bool} {saved output : State n}
    (h : Represents layout memory saved output) : Represents layout.flip memory output saved :=
  ⟨h.newJump,h.newMinimum,h.oldJump,h.oldMinimum⟩

@[simp] theorem budget_flip (layout : Layout) (index : List Bool) :
    budget layout.flip index = budget layout index := by
  simp only [budget,Layout.flip]
  omega

@[simp] theorem loopCost_flip (layout : Layout) (n : ℕ) : loopCost layout.flip n = loopCost layout n := by
  simp only [loopCost,budget_flip]

/-- The parity of the physical descriptors is mathematical bookkeeping;
Round.lean implements every change by moving the descriptor bit words. -/
def layoutAfter (layout : Layout) : ℕ → Layout
  | 0 => layout
  | k+1 => (layoutAfter layout k).flip

def stateAfter {n : ℕ} (saved : State n) : ℕ → State n
  | 0 => saved
  | k+1 => Doubling.step (Equiv.refl (Fin n)) (stateAfter saved k)

theorem stateAfter_run {n : ℕ} (p : Equiv.Perm (Fin n)) (k : ℕ) :
    stateAfter (Doubling.initial (Equiv.refl (Fin n)) p) k =
      Doubling.run (Equiv.refl (Fin n)) p k := by induction k <;> simp_all [stateAfter,Doubling.run]

@[simp] theorem layoutAfter_width (layout : Layout) (k : ℕ) :
    (layoutAfter layout k).width = layout.width := by induction k <;> simp_all [layoutAfter,Layout.flip]

@[simp] theorem budget_layoutAfter (layout : Layout) (k : ℕ) (index : List Bool) :
    budget (layoutAfter layout k) index = budget layout index := by
  induction k <;> simp_all [layoutAfter]

@[simp] theorem loopCost_layoutAfter (layout : Layout) (k n : ℕ) :
    loopCost (layoutAfter layout k) n = loopCost layout n := by simp only [loopCost,budget_layoutAfter]

theorem Layout.PingPong.after {layout : Layout} {n : ℕ} (h : layout.PingPong n) (k : ℕ) :
    (layoutAfter layout k).PingPong n := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih.flip

@[simp] theorem memoryFrame_flip (layout : Layout) (n : ℕ) (before after : ℕ → Bool) :
    MemoryFrame layout.flip n before after ↔ MemoryFrame layout n before after := by
  simp only [MemoryFrame,Outside,Layout.flip]
  constructor <;> intro h address ho <;> apply h address <;> tauto

@[simp] theorem memoryFrame_layoutAfter (layout : Layout) (k n : ℕ) (before after : ℕ → Bool) :
    MemoryFrame (layoutAfter layout k) n before after ↔ MemoryFrame layout n before after := by
  induction k <;> simp_all [layoutAfter]

end Maxwell.Cost.DoublingPass
