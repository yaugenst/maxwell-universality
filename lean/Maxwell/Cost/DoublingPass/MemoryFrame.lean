import Maxwell.Cost.DoublingPass.Encoding

namespace Maxwell.Cost.DoublingPass

/-- Addresses outside all four arrays used by a doubling pass. -/
def Outside (layout : Layout) (n address : ℕ) : Prop :=
  (address < layout.oldJump ∨ layout.oldJump + n * layout.width ≤ address) ∧
  (address < layout.oldMinimum ∨ layout.oldMinimum + n * layout.width ≤ address) ∧
  (address < layout.newJump ∨ layout.newJump + n * layout.width ≤ address) ∧
  (address < layout.newMinimum ∨ layout.newMinimum + n * layout.width ≤ address)

/-- A pass preserves every memory bit outside its four array intervals. -/
def MemoryFrame (layout : Layout) (n : ℕ) (before after : ℕ → Bool) : Prop :=
  ∀ address, Outside layout n address → after address = before address

theorem MemoryFrame.refl (layout : Layout) (n : ℕ) (memory : ℕ → Bool) :
    MemoryFrame layout n memory memory := fun _ _ => rfl

theorem MemoryFrame.trans {layout : Layout} {n : ℕ} {a b c : ℕ → Bool}
    (h : MemoryFrame layout n a b) (k : MemoryFrame layout n b c) :
    MemoryFrame layout n a c := fun address ha => (k address ha).trans (h address ha)

theorem MemoryFrame.of_eq {layout : Layout} {n : ℕ} {before after : ℕ → Bool}
    (h : after = before) : MemoryFrame layout n before after := by
  subst after
  exact MemoryFrame.refl layout n before

private theorem outside_slot {n base width address : ℕ} (i : Fin n)
    (h : address < base ∨ base + n * width ≤ address) :
    address < base + i.val * width ∨ base + i.val * width + width ≤ address := by
  have hi := Nat.mul_le_mul_right width (show i.val + 1 ≤ n by omega)
  rcases h with h | h
  · left
    omega
  · right
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using
      (Nat.add_le_add_left hi base).trans h

/-- The two exact slot writes cannot change an unrelated memory bit. -/
theorem slotMemory_frame {n : ℕ} (layout : Layout) (saved : State n) (i : Fin n)
    (memory : ℕ → Bool) : MemoryFrame layout n memory (slotMemory layout saved i memory) := by
  intro address ha
  unfold slotMemory
  rw [MemoryWord.writeBits_outside, MemoryWord.writeBits_outside]
  · simpa only [IncidenceEncoding.word_length] using outside_slot i ha.2.2.1
  · simpa only [IncidenceEncoding.word_length] using outside_slot i ha.2.2.2

private theorem separated_address {n base width other length : ℕ}
    (h : IncidenceEncoding.Separated base (n * width) other length)
    (i : Fin n) (j : ℕ) (hj : j < width) :
    base + i.val * width + j < other ∨ other + length ≤ base + i.val * width + j := by
  have hi := Nat.mul_le_mul_right width (show i.val + 1 ≤ n by omega)
  rcases h with h | h
  · left
    nlinarith
  · right
    omega

/-- Any represented array separated from the working regions survives
the memory frame, including the permutation needed by the color pass. -/
theorem MemoryFrame.represents {layout : Layout} {n m base width : ℕ}
    {before after : ℕ → Bool} {values : Vector (List Bool) m}
    (h : MemoryFrame layout n before after)
    (harray : BitArray.Represents before base width values)
    (hOldJump : IncidenceEncoding.Separated base (m * width)
      layout.oldJump (n * layout.width))
    (hOldMinimum : IncidenceEncoding.Separated base (m * width)
      layout.oldMinimum (n * layout.width))
    (hNewJump : IncidenceEncoding.Separated base (m * width)
      layout.newJump (n * layout.width))
    (hNewMinimum : IncidenceEncoding.Separated base (m * width)
      layout.newMinimum (n * layout.width)) :
    BitArray.Represents after base width values := by
  refine ⟨harray.length, ?_⟩
  intro i j hj
  rw [h _ ⟨separated_address hOldJump i j hj,
    separated_address hOldMinimum i j hj,
    separated_address hNewJump i j hj,
    separated_address hNewMinimum i j hj⟩]
  exact harray.bits i j hj

end Maxwell.Cost.DoublingPass
