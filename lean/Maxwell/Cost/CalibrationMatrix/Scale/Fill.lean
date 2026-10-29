import Maxwell.Cost.CalibrationMatrix.Scale.Row
import Maxwell.Cost.CalibrationMatrix.Fill

namespace Maxwell.Cost.CalibrationMatrix.Scale
variable {n : ℕ}

def payload (d : Data n) (words : Fin 4 → Vector (List Bool) n) (port : Fin 4) (i : Fin n) : List Bool :=
  FixedWidth.bits (addressValue d.width)
    (if port = 2 then positive d words i else negative d words i).bits

def filledWords (d : Data n) (words : Fin 4 → Vector (List Bool) n) (k : ℕ) :
    Fin 4 → Vector (List Bool) n :=
  fun port => if port.val < 2 then words port else fillPrefix (words port) (payload d words port) k

@[simp] theorem filledWords_zero (d : Data n) (words : Fin 4 → Vector (List Bool) n) :
    filledWords d words 0 = words := by
  funext port
  simp [filledWords]

@[simp] theorem positive_filled (d : Data n) (words : Fin 4 → Vector (List Bool) n) (k : ℕ) (i : Fin n) :
    positive d (filledWords d words k) i = positive d words i := by
  simp [positive, value, filledWords]
@[simp] theorem negative_filled (d : Data n) (words : Fin 4 → Vector (List Bool) n) (k : ℕ) (i : Fin n) :
    negative d (filledWords d words k) i = negative d words i := by
  simp [negative, value, filledWords]

theorem filledWords_step (d : Data n) (words : Fin 4 → Vector (List Bool) n) (i : Fin n) :
    rowWords d (filledWords d words i.val) i = filledWords d words (i.val+1) := by
  funext port
  fin_cases port <;> simp [rowWords, setPair, filledWords, positive, negative, value]
  · exact fillPrefix_step (words 2) (payload d words 2) i
  · exact fillPrefix_step (words 3) (payload d words 3) i

def Outside (d : Data n) (s t : BitRAMState) : Prop :=
  ∀ address, (∀ port : Fin 4, 2 ≤ port.val →
    address < addressValue (d.bases port) ∨ addressValue (d.bases port)+n*addressValue d.width ≤ address) →
    t.memory address = s.memory address

theorem Outside.refl (d : Data n) (s : BitRAMState) : Outside d s s := fun _ _ => rfl

theorem Outside.trans {d : Data n} {s t u : BitRAMState}
    (h : Outside d s t) (k : Outside d t u) : Outside d s u :=
  fun a ha => (k a ha).trans (h a ha)

theorem Outside.of_memory {d : Data n} {s t : BitRAMState}
    (h : t.memory = s.memory) : Outside d s t := by intro a _; rw [h]

theorem Outside.of_row {d : Data n} {words : Fin 4 → Vector (List Bool) n}
    (i : Fin n) {s t : BitRAMState} (hm : t.memory = rowMemory d words i s.memory) : Outside d s t := by
  intro a ha
  have hslot := Nat.mul_le_mul_right (addressValue d.width) (show i.val+1 ≤ n by omega)
  have outside (port : Fin 4) (hp : 2 ≤ port.val) (bits : List Bool) :
      a < addressValue (d.bases port)+i.val*addressValue d.width ∨
        addressValue (d.bases port)+i.val*addressValue d.width+
          (FixedWidth.bits (addressValue d.width) bits).length ≤ a := by
    rw [FixedWidth.bits_length]
    rcases ha port hp with h | h
    · left; omega
    · right; nlinarith
  rw [hm]
  unfold rowMemory
  rw [MemoryWord.writeBits_outside _ _ _ _ (outside 3 (by decide) _),
    MemoryWord.writeBits_outside _ _ _ _ (outside 2 (by decide) _)]

end Maxwell.Cost.CalibrationMatrix.Scale
