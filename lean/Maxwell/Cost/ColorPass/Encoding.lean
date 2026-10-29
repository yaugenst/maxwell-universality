import Maxwell.Cost.DoublingPass.Common

/-! One-bit output memory for comparisons of saved cycle-minimum labels. -/
namespace Maxwell.Cost.ColorPass
open DoublingPass (Layout State words)

def bit {n : ℕ} (saved : State n) (i : Fin n) : Bool :=
  decide (saved.minimum.get i < saved.minimum.get (saved.jump.get i))

def colors {n : ℕ} (saved : State n) : Vector Bool n := Vector.ofFn (bit saved)

def colorWords {n : ℕ} (values : Vector Bool n) : Vector (List Bool) n :=
  values.map (fun b => [b])

@[simp] theorem colorWords_get {n : ℕ} (values : Vector Bool n) (i : Fin n) :
    (colorWords values).get i = [values.get i] := by simp [colorWords, Vector.get, Fin.cast]

@[simp] theorem colorWords_set {n : ℕ} (values : Vector Bool n) (i : Fin n) (b : Bool) :
    colorWords (values.set i b) = (colorWords values).set i [b] := by simp [colorWords, Vector.map_set]

structure Separated (layout : Layout) (n : ℕ) : Prop where
  jump : IncidenceEncoding.Separated layout.oldJump (n * layout.width) layout.newJump n
  minimum : IncidenceEncoding.Separated layout.oldMinimum (n * layout.width) layout.newJump n

structure Represents {n : ℕ} (layout : Layout) (memory : ℕ → Bool)
    (saved : State n) (output : Vector Bool n) : Prop where
  jump : BitArray.Represents memory layout.oldJump layout.width (words layout.width saved.jump)
  minimum : BitArray.Represents memory layout.oldMinimum layout.width (words layout.width saved.minimum)
  output : BitArray.Represents memory layout.newJump 1 (colorWords output)

def slotMemory {n : ℕ} (layout : Layout) (saved : State n) (i : Fin n)
    (memory : ℕ → Bool) : ℕ → Bool := MemoryWord.writeBits memory (layout.newJump + i.val) [bit saved i]

theorem represents_slot {n : ℕ} {layout : Layout} {memory : ℕ → Bool}
    {saved : State n} {output : Vector Bool n} (h : Represents layout memory saved output)
    (hs : Separated layout n) (i : Fin n) :
    Represents layout (slotMemory layout saved i memory) saved (output.set i (bit saved i)) := by
  constructor
  · simpa only [slotMemory, Nat.mul_one] using
      IncidenceEncoding.represents_write_disjoint h.jump layout.newJump 1 i [bit saved i] rfl
        (by simpa only [Nat.mul_one] using hs.jump)
  · simpa only [slotMemory, Nat.mul_one] using
      IncidenceEncoding.represents_write_disjoint h.minimum layout.newJump 1 i [bit saved i] rfl
        (by simpa only [Nat.mul_one] using hs.minimum)
  · simpa only [slotMemory, Nat.mul_one, colorWords_set] using h.output.write i [bit saved i] rfl

def fill {n : ℕ} (saved : State n) (output : Vector Bool n) : (limit : ℕ) → limit ≤ n → Vector Bool n
  | 0, _ => output
  | limit + 1, hl => (fill saved output limit (by omega)).set limit (bit saved ⟨limit, by omega⟩) (by omega)

theorem fill_get {n : ℕ} (saved : State n) (output : Vector Bool n)
    (limit : ℕ) (hl : limit ≤ n) (j : Fin n) :
    (fill saved output limit hl).get j = if j.val < limit then bit saved j else output.get j := by
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

theorem fill_complete {n : ℕ} (saved : State n) (output : Vector Bool n) :
    fill saved output n le_rfl = colors saved := by
  apply Vector.ext
  intro j hj
  have h := fill_get saved output n le_rfl ⟨j, hj⟩
  simpa [hj, colors, Vector.get, Fin.cast] using h

end Maxwell.Cost.ColorPass
