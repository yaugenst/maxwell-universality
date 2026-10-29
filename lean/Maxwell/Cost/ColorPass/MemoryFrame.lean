import Maxwell.Cost.ColorPass.Encoding

namespace Maxwell.Cost.ColorPass
open DoublingPass

/-- Only the color output bit interval may change. -/
def MemoryFrame (layout : Layout) (n : ℕ) (before after : ℕ → Bool) : Prop :=
  ∀ address, address < layout.newJump ∨ layout.newJump+n ≤ address → after address = before address

theorem MemoryFrame.refl (layout : Layout) (n : ℕ) (memory : ℕ → Bool) :
    MemoryFrame layout n memory memory := fun _ _ => rfl

theorem MemoryFrame.trans {layout : Layout} {n : ℕ} {a b c : ℕ → Bool}
    (h : MemoryFrame layout n a b) (k : MemoryFrame layout n b c) : MemoryFrame layout n a c :=
  fun address ha => (k address ha).trans (h address ha)

theorem slotMemory_frame {n : ℕ} (layout : Layout) (saved : State n) (j : Fin n)
    (memory : ℕ → Bool) : MemoryFrame layout n memory (slotMemory layout saved j memory) := by
  intro address ha
  apply MemoryWord.writeBits_outside
  have hj := j.isLt
  simp only [List.length_singleton]
  omega

end Maxwell.Cost.ColorPass
