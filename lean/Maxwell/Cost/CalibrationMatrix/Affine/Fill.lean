import Maxwell.Cost.CalibrationMatrix.Affine.RowCore
import Maxwell.Cost.CalibrationMatrix.Fill

namespace Maxwell.Cost.CalibrationMatrix.Affine
variable {n : ℕ}

def payload (d : Data n) (words : Fin 10 → Vector (List Bool) n) (port : Fin 10) (i : Fin n) : List Bool :=
  FixedWidth.bits (addressValue d.width)
    (if port = 6 then newWPositive d words i else if port = 7 then newWNegative d words i
      else if port = 8 then newXPositive d words i else newXNegative d words i).bits

def filledWords (d : Data n) (words : Fin 10 → Vector (List Bool) n) (k : ℕ) :
    Fin 10 → Vector (List Bool) n :=
  fun port => if port.val < 6 then words port else fillPrefix (words port) (payload d words port) k

@[simp] theorem filledWords_zero (d : Data n) (words : Fin 10 → Vector (List Bool) n) :
    filledWords d words 0 = words := by
  funext port
  simp [filledWords]

@[simp] theorem newWPositive_filled (d : Data n) (words : Fin 10 → Vector (List Bool) n) (k : ℕ) (i : Fin n) :
    newWPositive d (filledWords d words k) i = newWPositive d words i := by
  simp [newWPositive, value, filledWords]
@[simp] theorem newWNegative_filled (d : Data n) (words : Fin 10 → Vector (List Bool) n) (k : ℕ) (i : Fin n) :
    newWNegative d (filledWords d words k) i = newWNegative d words i := by
  simp [newWNegative, value, filledWords]
@[simp] theorem newXPositive_filled (d : Data n) (words : Fin 10 → Vector (List Bool) n) (k : ℕ) (i : Fin n) :
    newXPositive d (filledWords d words k) i = newXPositive d words i := by
  simp [newXPositive, partialPositive, newWPositive, value, filledWords]
@[simp] theorem newXNegative_filled (d : Data n) (words : Fin 10 → Vector (List Bool) n) (k : ℕ) (i : Fin n) :
    newXNegative d (filledWords d words k) i = newXNegative d words i := by
  simp [newXNegative, partialNegative, newWNegative, value, filledWords]

theorem filledWords_step (d : Data n) (words : Fin 10 → Vector (List Bool) n) (i : Fin n) :
    rowWords d (filledWords d words i.val) i = filledWords d words (i.val+1) := by
  funext port
  fin_cases port <;>
    simp [rowWords, wWords, setPair, filledWords,
      newWPositive, newWNegative, newXPositive, newXNegative, partialPositive, partialNegative, value]
  · exact fillPrefix_step (words 6) (payload d words 6) i
  · exact fillPrefix_step (words 7) (payload d words 7) i
  · exact fillPrefix_step (words 8) (payload d words 8) i
  · exact fillPrefix_step (words 9) (payload d words 9) i

def Outside (d : Data n) (s t : BitRAMState) : Prop :=
  ∀ address, (∀ port : Fin 10, 6 ≤ port.val →
    address < addressValue (d.bases port) ∨ addressValue (d.bases port)+n*addressValue d.width ≤ address) →
    t.memory address = s.memory address

theorem Outside.refl (d : Data n) (s : BitRAMState) : Outside d s s := fun _ _ => rfl

theorem Outside.trans {d : Data n} {s t u : BitRAMState}
    (h : Outside d s t) (k : Outside d t u) : Outside d s u :=
  fun a ha => (k a ha).trans (h a ha)

theorem Outside.of_memory {d : Data n} {s t : BitRAMState}
    (h : t.memory = s.memory) : Outside d s t := by intro a _; rw [h]

theorem Outside.of_row {d : Data n} {words : Fin 10 → Vector (List Bool) n}
    (i : Fin n) {s t : BitRAMState} (hm : t.memory = rowMemory d words i s.memory) : Outside d s t := by
  intro a ha
  have hslot := Nat.mul_le_mul_right (addressValue d.width) (show i.val+1 ≤ n by omega)
  have outside (port : Fin 10) (hp : 6 ≤ port.val) (bits : List Bool) :
      a < addressValue (d.bases port)+i.val*addressValue d.width ∨
        addressValue (d.bases port)+i.val*addressValue d.width+
          (FixedWidth.bits (addressValue d.width) bits).length ≤ a := by
    rw [FixedWidth.bits_length]
    rcases ha port hp with h | h
    · left; omega
    · right; nlinarith
  rw [hm]
  unfold rowMemory
  rw [MemoryWord.writeBits_outside _ _ _ _ (outside 9 (by decide) _),
    MemoryWord.writeBits_outside _ _ _ _ (outside 8 (by decide) _),
    MemoryWord.writeBits_outside _ _ _ _ (outside 7 (by decide) _),
    MemoryWord.writeBits_outside _ _ _ _ (outside 6 (by decide) _)]

end Maxwell.Cost.CalibrationMatrix.Affine
