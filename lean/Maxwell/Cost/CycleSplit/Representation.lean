import Maxwell.Cost.CycleSplit.Adapter
import Maxwell.Cost.DoublingInit

namespace Maxwell.Cost.CycleSplit
open DoublingPass
open Maxwell.Logical.Routing

def Apart (layout : Layout) (base n : ℕ) : Prop :=
  IncidenceEncoding.Separated base (n*layout.width) layout.oldJump (n*layout.width) ∧
  IncidenceEncoding.Separated base (n*layout.width) layout.oldMinimum (n*layout.width) ∧
  IncidenceEncoding.Separated base (n*layout.width) layout.newJump (n*layout.width) ∧
  IncidenceEncoding.Separated base (n*layout.width) layout.newMinimum (n*layout.width)

theorem Apart.flip {layout : Layout} {base n : ℕ} (h : Apart layout base n) : Apart layout.flip base n :=
  ⟨h.2.2.1,h.2.2.2,h.1,h.2.1⟩

theorem Apart.after {layout : Layout} {base n : ℕ} (h : Apart layout base n) (k : ℕ) :
    Apart (layoutAfter layout k) base n := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih.flip

theorem inputA_apart {layout : DoublingInit.Layout} {n : ℕ} (h : layout.Separated n) :
    Apart layout.route layout.inputA n :=
  ⟨h 0 2 (by decide),h 0 3 (by decide),h 0 4 (by decide),h 0 5 (by decide)⟩

theorem Apart.represents {layout : Layout} {base n : ℕ} {before after : ℕ → Bool}
    {values : Vector (List Bool) n} (h : Apart layout base n)
    (mf : MemoryFrame layout n before after) (r : BitArray.Represents before base layout.width values) :
    BitArray.Represents after base layout.width values := mf.represents r h.1 h.2.1 h.2.2.1 h.2.2.2

theorem color_represents {n : ℕ} (layout : Layout) (pairingBase : ℕ) (a b : Equiv.Perm (Fin n))
    (rounds : ℕ) (memory : ℕ → Bool) (output : State n)
    (rp : BitArray.Represents memory pairingBase layout.width (words layout.width (DoublingInit.permutation a)))
    (rm : Represents layout memory (stateAfter (Doubling.initial (Equiv.refl (Fin n)) (a*b)) rounds) output) :
    ColorPass.Represents (colorLayout layout pairingBase) memory (ColorPass.comparisonState a b rounds)
      (snapshotColors memory layout.newJump n) := by
  refine ⟨rp,?_,snapshotColors_represents _ _ _⟩
  simpa only [stateAfter_run,colorLayout,ColorPass.comparisonState] using rm.oldMinimum

theorem color_separated {layout : Layout} {pairingBase n : ℕ}
    (hw : 0<layout.width) (hp : layout.PingPong n) (ha : Apart layout pairingBase n) :
    ColorPass.Separated (colorLayout layout pairingBase) n := by
  have hn : n≤n*layout.width := by nlinarith
  have shrink {base : ℕ} (h : IncidenceEncoding.Separated base (n*layout.width) layout.newJump (n*layout.width)) :
      IncidenceEncoding.Separated base (n*layout.width) layout.newJump n := by
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  exact ⟨shrink ha.2.2.1,shrink hp.forward.minimumJump⟩

theorem color_memory_frame {layout : Layout} {pairingBase n : ℕ} {before after : ℕ → Bool}
    (hw : 0<layout.width) (h : ColorPass.MemoryFrame (colorLayout layout pairingBase) n before after) :
    MemoryFrame layout n before after := by
  intro address outside
  apply h address
  have hn : n≤n*layout.width := by nlinarith
  rcases outside.2.2.1 with hl | hr
  · exact Or.inl hl
  · exact Or.inr (by dsimp [colorLayout]; omega)

end Maxwell.Cost.CycleSplit
