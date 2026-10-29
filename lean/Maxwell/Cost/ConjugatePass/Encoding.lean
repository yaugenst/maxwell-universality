import Maxwell.Cost.DoublingPass.Common

/-! Cached conjugation of a pairing by a stored permutation. -/
namespace Maxwell.Cost.ConjugatePass
open DoublingPass (Layout State words)

structure Tables (n : ℕ) where
  forward : Vector (Fin n) n
  pairing : Vector (Fin n) n
  backward : Vector (Fin n) n

def value {n : ℕ} (saved : Tables n) (i : Fin n) : Fin n :=
  saved.backward.get (saved.pairing.get (saved.forward.get i))

def composed {n : ℕ} (saved : Tables n) : Vector (Fin n) n := Vector.ofFn (value saved)

structure Separated (layout : Layout) (n : ℕ) : Prop where
  forward : IncidenceEncoding.Separated layout.oldJump (n * layout.width) layout.newMinimum (n * layout.width)
  pairing : IncidenceEncoding.Separated layout.oldMinimum (n * layout.width) layout.newMinimum (n * layout.width)
  backward : IncidenceEncoding.Separated layout.newJump (n * layout.width) layout.newMinimum (n * layout.width)

structure Represents {n : ℕ} (layout : Layout) (memory : ℕ → Bool)
    (saved : Tables n) (output : Vector (List Bool) n) : Prop where
  forward : BitArray.Represents memory layout.oldJump layout.width (words layout.width saved.forward)
  pairing : BitArray.Represents memory layout.oldMinimum layout.width (words layout.width saved.pairing)
  backward : BitArray.Represents memory layout.newJump layout.width (words layout.width saved.backward)
  output : BitArray.Represents memory layout.newMinimum layout.width output

def slotMemory {n : ℕ} (layout : Layout) (saved : Tables n) (i : Fin n)
    (memory : ℕ → Bool) : ℕ → Bool := MemoryWord.writeBits memory
      (layout.newMinimum + i.val * layout.width) (IncidenceEncoding.word layout.width (value saved i).val)

theorem represents_slot {n : ℕ} {layout : Layout} {memory : ℕ → Bool}
    {saved : Tables n} {output : Vector (List Bool) n} (h : Represents layout memory saved output)
    (hs : Separated layout n) (i : Fin n) :
    Represents layout (slotMemory layout saved i memory) saved (output.set i (IncidenceEncoding.word layout.width (value saved i).val)) := by
  constructor
  · exact IncidenceEncoding.represents_write_disjoint h.forward layout.newMinimum layout.width i _
      (IncidenceEncoding.word_length _ _) hs.forward
  · exact IncidenceEncoding.represents_write_disjoint h.pairing layout.newMinimum layout.width i _
      (IncidenceEncoding.word_length _ _) hs.pairing
  · exact IncidenceEncoding.represents_write_disjoint h.backward layout.newMinimum layout.width i _
      (IncidenceEncoding.word_length _ _) hs.backward
  · simpa only [slotMemory] using
      h.output.write i (IncidenceEncoding.word layout.width (value saved i).val) (IncidenceEncoding.word_length _ _)

def fill {n : ℕ} (width : ℕ) (saved : Tables n) (output : Vector (List Bool) n) : (limit : ℕ) → limit ≤ n → Vector (List Bool) n
  | 0, _ => output
  | limit + 1, hl => (fill width saved output limit (by omega)).set limit (IncidenceEncoding.word width (value saved ⟨limit, by omega⟩).val) (by omega)

theorem fill_get {n : ℕ} (width : ℕ) (saved : Tables n) (output : Vector (List Bool) n)
    (limit : ℕ) (hl : limit ≤ n) (j : Fin n) :
    (fill width saved output limit hl).get j = if j.val < limit then IncidenceEncoding.word width (value saved j).val else output.get j := by
  induction limit with
  | zero => simp [fill]
  | succ limit ih =>
    rw [fill, Maxwell.Logical.Routing.DummyFill.get_set _ ⟨limit, by omega⟩ j]
    by_cases he : (⟨limit, by omega⟩ : Fin n) = j
    · have hj : j.val = limit := (congrArg Fin.val he).symm
      simp [he, hj]
    · have hj : j.val ≠ limit := fun h => he (Fin.ext h.symm)
      simp only [he, ↓reduceIte, ih (by omega)]
      have hiff : j.val < limit + 1 ↔ j.val < limit := by omega
      simp only [hiff]

theorem fill_complete {n : ℕ} (width : ℕ) (saved : Tables n) (output : Vector (List Bool) n) :
    fill width saved output n le_rfl = words width (composed saved) := by
  apply Vector.ext
  intro j hj
  have h := fill_get width saved output n le_rfl ⟨j, hj⟩
  simpa [hj, words, IncidenceEncoding.words, composed, Vector.get, Fin.cast] using h

end Maxwell.Cost.ConjugatePass
