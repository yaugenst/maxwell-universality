import Maxwell.Cost.CalibrationMatrix.Rows

namespace Maxwell.Cost.CalibrationMatrix

def OutputOutside (l : OutputLayout) (rows width : ℕ) (s t : BitRAMState) : Prop :=
  ∀ address,
    (address < addressValue l.positiveBase ∨ addressValue l.positiveBase+rows*width ≤ address) →
    (address < addressValue l.negativeBase ∨ addressValue l.negativeBase+rows*width ≤ address) →
    t.memory address = s.memory address

theorem OutputOutside.refl (l : OutputLayout) (rows width : ℕ) (s : BitRAMState) :
    OutputOutside l rows width s s := by intro a _ _; rfl

theorem OutputOutside.trans {l : OutputLayout} {rows width : ℕ} {s t u : BitRAMState}
    (h : OutputOutside l rows width s t) (k : OutputOutside l rows width t u) :
    OutputOutside l rows width s u := fun a hp hn => (k a hp hn).trans (h a hp hn)

theorem OutputOutside.of_memory {l : OutputLayout} {rows width : ℕ} {s t : BitRAMState}
    (h : t.memory = s.memory) : OutputOutside l rows width s t := by intro a _ _; rw [h]

theorem OutputOutside.of_write {l : OutputLayout} {rows width : ℕ} {s t : BitRAMState}
    (row : Fin rows) (positive negative : List Bool)
    (hp : positive.length = width) (hn : negative.length = width)
    (hm : t.memory = MemoryWord.writeBits
      (MemoryWord.writeBits s.memory (addressValue l.positiveBase+row.val*width) positive)
      (addressValue l.negativeBase+row.val*width) negative) :
    OutputOutside l rows width s t := by
  intro a hap han
  have hslot := Nat.mul_le_mul_right width (show row.val+1 ≤ rows by omega)
  have outside (base : ℕ) (h : a < base ∨ base+rows*width ≤ a) :
      a < base+row.val*width ∨ base+row.val*width+width ≤ a := by
    rcases h with h | h
    · left; omega
    · right; nlinarith
  rw [hm, MemoryWord.writeBits_outside _ _ _ _ (by simpa only [hn] using outside _ han),
    MemoryWord.writeBits_outside _ _ _ _ (by simpa only [hp] using outside _ hap)]

end Maxwell.Cost.CalibrationMatrix
