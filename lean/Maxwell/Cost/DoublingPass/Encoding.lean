import Maxwell.Cost.IncidenceEncoding
import Maxwell.Logical.Routing.Doubling

namespace Maxwell.Cost.DoublingPass
open Maxwell.Logical.Routing
open IncidenceEncoding (Separated)

abbrev State (n : ℕ) := Doubling.State (Fin n) n

def words {n : ℕ} (width : ℕ) (values : Vector (Fin n) n) : Vector (List Bool) n :=
  IncidenceEncoding.words width (values.map Fin.val)

@[simp] theorem words_get {n : ℕ} (width : ℕ) (values : Vector (Fin n) n) (i : Fin n) :
    (words width values).get i = IncidenceEncoding.word width (values.get i).val := by
  rw [words, IncidenceEncoding.words_get]
  simp [Vector.get, Fin.cast]

@[simp] theorem words_set {n : ℕ} (width : ℕ) (values : Vector (Fin n) n) (i value : Fin n) :
    words width (values.set i.val value i.isLt) =
      (words width values).set i.val (IncidenceEncoding.word width value.val) i.isLt := by
  simp only [words, Vector.map_set, IncidenceEncoding.words_set]

structure Layout where
  width : ℕ
  oldJump : ℕ
  oldMinimum : ℕ
  newJump : ℕ
  newMinimum : ℕ

structure Layout.Separated (layout : Layout) (n : ℕ) : Prop where
  jumpJump : IncidenceEncoding.Separated layout.oldJump (n * layout.width) layout.newJump (n * layout.width)
  jumpMinimum : IncidenceEncoding.Separated layout.oldJump (n * layout.width) layout.newMinimum (n * layout.width)
  minimumJump : IncidenceEncoding.Separated layout.oldMinimum (n * layout.width) layout.newJump (n * layout.width)
  minimumMinimum : IncidenceEncoding.Separated layout.oldMinimum (n * layout.width) layout.newMinimum (n * layout.width)
  outputs : IncidenceEncoding.Separated layout.newJump (n * layout.width) layout.newMinimum (n * layout.width)

/-- Old arrays may share an interval if their represented contents coincide;
every written output interval is separated from both saved arrays. -/
structure Represents {n : ℕ} (layout : Layout) (memory : ℕ → Bool) (saved output : State n) : Prop where
  oldJump : BitArray.Represents memory layout.oldJump layout.width (words layout.width saved.jump)
  oldMinimum : BitArray.Represents memory layout.oldMinimum layout.width (words layout.width saved.minimum)
  newJump : BitArray.Represents memory layout.newJump layout.width (words layout.width output.jump)
  newMinimum : BitArray.Represents memory layout.newMinimum layout.width (words layout.width output.minimum)

def slot {n : ℕ} (saved output : State n) (i : Fin n) : State n :=
  ⟨output.jump.set i.val (saved.jump.get (saved.jump.get i)) i.isLt,
   output.minimum.set i.val (min (saved.minimum.get i) (saved.minimum.get (saved.jump.get i))) i.isLt⟩

def slotMemory {n : ℕ} (layout : Layout) (saved : State n) (i : Fin n)
    (memory : ℕ → Bool) : ℕ → Bool :=
  MemoryWord.writeBits
    (MemoryWord.writeBits memory (layout.newJump + i.val * layout.width)
      (IncidenceEncoding.word layout.width (saved.jump.get (saved.jump.get i)).val))
    (layout.newMinimum + i.val * layout.width)
      (IncidenceEncoding.word layout.width
        (min (saved.minimum.get i) (saved.minimum.get (saved.jump.get i))).val)

theorem represents_slot {n : ℕ} {layout : Layout} {memory : ℕ → Bool} {saved output : State n}
    (h : Represents layout memory saved output) (hs : layout.Separated n) (i : Fin n) :
    Represents layout (slotMemory layout saved i memory) saved (slot saved output i) := by
  let jumpWord := IncidenceEncoding.word layout.width (saved.jump.get (saved.jump.get i)).val
  let minWord := IncidenceEncoding.word layout.width
    (min (saved.minimum.get i) (saved.minimum.get (saved.jump.get i))).val
  have oldJ := IncidenceEncoding.represents_write_disjoint h.oldJump layout.newJump layout.width i
    jumpWord (by simp [jumpWord]) hs.jumpJump
  have oldM := IncidenceEncoding.represents_write_disjoint h.oldMinimum layout.newJump layout.width i
    jumpWord (by simp [jumpWord]) hs.minimumJump
  have newM := IncidenceEncoding.represents_write_disjoint h.newMinimum layout.newJump layout.width i
    jumpWord (by simp [jumpWord]) hs.outputs.symm
  have newJ := h.newJump.write i jumpWord (by simp [jumpWord])
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact IncidenceEncoding.represents_write_disjoint oldJ layout.newMinimum layout.width i
      minWord (by simp [minWord]) hs.jumpMinimum
  · exact IncidenceEncoding.represents_write_disjoint oldM layout.newMinimum layout.width i
      minWord (by simp [minWord]) hs.minimumMinimum
  · simpa only [slot, slotMemory, words_set, jumpWord, minWord] using
      IncidenceEncoding.represents_write_disjoint newJ layout.newMinimum layout.width i
        minWord (by simp [minWord]) hs.outputs
  · simpa only [slot, slotMemory, words_set, jumpWord, minWord] using
      newM.write i minWord (by simp [minWord])

/-- The ordered output-filling recursion shares the fixed saved arrays. -/
def fill {n : ℕ} (saved output : State n) : (limit : ℕ) → limit ≤ n → State n
  | 0, _ => output
  | limit + 1, hl => slot saved (fill saved output limit (by omega)) ⟨limit, by omega⟩

theorem fill_jump {n : ℕ} (saved output : State n) (limit : ℕ) (hl : limit ≤ n) (j : Fin n) :
    (fill saved output limit hl).jump.get j =
      if j.val < limit then saved.jump.get (saved.jump.get j) else output.jump.get j := by
  induction limit with
  | zero => simp [fill]
  | succ limit ih =>
    simp only [fill, slot]
    rw [DummyFill.get_set _ ⟨limit, by omega⟩ j]
    by_cases he : (⟨limit, by omega⟩ : Fin n) = j
    · have hj : j.val = limit := (congrArg Fin.val he).symm
      simp [he, hj]
    · have hj : j.val ≠ limit := fun h => he (Fin.ext h.symm)
      simp only [he, ↓reduceIte, ih (by omega)]
      have hiff : j.val < limit + 1 ↔ j.val < limit := by omega
      simp only [hiff]

theorem fill_minimum {n : ℕ} (saved output : State n) (limit : ℕ) (hl : limit ≤ n) (j : Fin n) :
    (fill saved output limit hl).minimum.get j =
      if j.val < limit then min (saved.minimum.get j) (saved.minimum.get (saved.jump.get j))
      else output.minimum.get j := by
  induction limit with
  | zero => simp [fill]
  | succ limit ih =>
    simp only [fill, slot]
    rw [DummyFill.get_set _ ⟨limit, by omega⟩ j]
    by_cases he : (⟨limit, by omega⟩ : Fin n) = j
    · have hj : j.val = limit := (congrArg Fin.val he).symm
      simp [he, hj]
    · have hj : j.val ≠ limit := fun h => he (Fin.ext h.symm)
      simp only [he, ↓reduceIte, ih (by omega)]
      have hiff : j.val < limit + 1 ↔ j.val < limit := by omega
      simp only [hiff]

/-- Filling every output slot is the actual cached pointer-doubling step. -/
theorem fill_complete {n : ℕ} (saved output : State n) :
    fill saved output n le_rfl = Doubling.step (Equiv.refl (Fin n)) saved := by
  cases hfill : fill saved output n le_rfl with
  | mk jump minimum =>
    have hj : jump = (Doubling.step (Equiv.refl (Fin n)) saved).jump := by
      apply Vector.ext
      intro j hj
      have h := fill_jump saved output n le_rfl ⟨j, hj⟩
      simpa [hfill, hj, Doubling.step, Doubling.jumpAt, Vector.get, Fin.cast] using h
    have hm : minimum = (Doubling.step (Equiv.refl (Fin n)) saved).minimum := by
      apply Vector.ext
      intro j hj
      have h := fill_minimum saved output n le_rfl ⟨j, hj⟩
      simpa [hfill, hj, Doubling.step, Doubling.minAt, Vector.get, Fin.cast] using h
    cases hj
    cases hm
    rfl

end Maxwell.Cost.DoublingPass
