import Maxwell.Cost.ConjugatePass.Encoding

namespace Maxwell.Cost.ConjugatePass
open DoublingPass

/-- Only the composed lookup output interval may change. -/
def MemoryFrame (layout : Layout) (n : ℕ) (before after : ℕ → Bool) : Prop :=
  ∀ address, address < layout.newMinimum ∨ layout.newMinimum+n*layout.width ≤ address → after address = before address

theorem MemoryFrame.refl (layout : Layout) (n : ℕ) (memory : ℕ → Bool) :
    MemoryFrame layout n memory memory := fun _ _ => rfl

theorem MemoryFrame.trans {layout : Layout} {n : ℕ} {a b c : ℕ → Bool}
    (h : MemoryFrame layout n a b) (k : MemoryFrame layout n b c) : MemoryFrame layout n a c :=
  fun address ha => (k address ha).trans (h address ha)

theorem slotMemory_frame {n : ℕ} (layout : Layout) (saved : Tables n) (j : Fin n)
    (memory : ℕ → Bool) : MemoryFrame layout n memory (slotMemory layout saved j memory) := by
  intro address ha
  apply MemoryWord.writeBits_outside
  have hj := j.isLt
  simp only [IncidenceEncoding.word_length]
  have hmul := Nat.mul_le_mul_right layout.width (Nat.succ_le_of_lt hj)
  simp only [Nat.succ_mul] at hmul
  omega

end Maxwell.Cost.ConjugatePass
