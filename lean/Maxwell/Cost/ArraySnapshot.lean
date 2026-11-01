import Maxwell.Cost.Array

/-! Exact finite views of existing memory, independent of allocation or initialization. -/
namespace Maxwell.Cost.BitArray

/-- Every finite memory interval has an exact saved-word view. This is only
a specification for the existing bits, not a runtime memory-reading oracle. -/
def snapshot (memory : ℕ → Bool) (base width n : ℕ) : Vector (List Bool) n :=
  Vector.ofFn (fun i => MemoryWord.readBits memory (base+i.val*width) width)

@[simp] theorem snapshot_get (memory : ℕ → Bool) (base width n : ℕ) (i : Fin n) :
    (snapshot memory base width n).get i = MemoryWord.readBits memory (base+i.val*width) width := by
  simp [snapshot,Vector.get,Fin.cast]

theorem snapshot_represents (memory : ℕ → Bool) (base width n : ℕ) :
    Represents memory base width (snapshot memory base width n) where
  length i := by simp only [snapshot_get,MemoryWord.readBits_length]
  bits i j hj := by
    simp only [snapshot_get]
    exact (MemoryWord.readBits_getElem memory _ width j hj).symm

#print axioms snapshot_represents
end Maxwell.Cost.BitArray
