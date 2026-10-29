import Maxwell.Cost.HalfPair.Words
import Maxwell.Cost.ConjugatePass.MemoryFrame
import Maxwell.Cost.DoublingInit.Common

namespace Maxwell.Cost.HalfPair
open Maxwell.Logical.Routing.Coloring.NumericSplit

def array (k : ℕ) : Vector (List Bool) (2*(2^k)) :=
  Vector.ofFn (fun i => SourceCircuit.fixedWidth (k+2) (halfSwap (2^k) i).val)

def fill (k : ℕ) (output : Vector (List Bool) (2*(2^k))) : (limit : ℕ) → limit ≤ 2*(2^k) → Vector (List Bool) (2*(2^k))
  | 0, _ => output
  | limit+1, hl => (fill k output limit (by omega)).set limit ((array k).get ⟨limit,by omega⟩) (by omega)

theorem fill_get (k : ℕ) (output : Vector (List Bool) (2*(2^k)))
    (limit : ℕ) (hl : limit ≤ 2*(2^k)) (j : Fin (2*(2^k))) :
    (fill k output limit hl).get j = if j.val < limit then (array k).get j else output.get j := by
  induction limit with
  | zero => simp [fill]
  | succ limit ih =>
    rw [fill,Maxwell.Logical.Routing.DummyFill.get_set _ ⟨limit,by omega⟩ j]
    by_cases he : (⟨limit,by omega⟩ : Fin (2*(2^k)))=j
    · have hj : j.val=limit := (congrArg Fin.val he).symm
      simp [he,hj]
    · have hj : j.val≠limit := fun h => he (Fin.ext h.symm)
      simp only [he,↓reduceIte,ih (by omega)]
      have hiff : j.val<limit+1 ↔ j.val<limit := by omega
      simp only [hiff]

theorem fill_complete (k : ℕ) (output : Vector (List Bool) (2*(2^k))) :
    fill k output (2*(2^k)) le_rfl = array k := by
  apply Vector.ext
  intro i hi
  simpa [hi,Vector.get,Fin.cast] using fill_get k output (2*(2^k)) le_rfl ⟨i,hi⟩

abbrev Represents (layout : DoublingInit.Layout) (memory : ℕ → Bool) {k : ℕ}
    (output : Vector (List Bool) (2*(2^k))) :=
  BitArray.Represents memory layout.route.newMinimum layout.route.width output

abbrev MemoryFrame (layout : DoublingInit.Layout) (k : ℕ) (before after : ℕ → Bool) :=
  ConjugatePass.MemoryFrame layout.route (2*(2^k)) before after

def slotMemory (layout : DoublingInit.Layout) (k : ℕ) (i : Fin (2*(2^k)))
    (memory : ℕ → Bool) : ℕ → Bool := MemoryWord.writeBits memory
      (layout.route.newMinimum+i.val*layout.route.width) ((array k).get i)

theorem slotMemory_frame (layout : DoublingInit.Layout) (k : ℕ) (i : Fin (2*(2^k)))
    (hw : layout.route.width=k+2) (memory : ℕ → Bool) :
    MemoryFrame layout k memory (slotMemory layout k i memory) := by
  intro address ha
  apply MemoryWord.writeBits_outside
  have hlen : ((array k).get i).length=layout.route.width := by simp [array,Vector.get,Fin.cast,hw]
  rw [hlen]
  have hmul : i.val*layout.route.width+layout.route.width ≤ (2*(2^k))*layout.route.width := by
    nlinarith [Nat.mul_le_mul_right layout.route.width (Nat.succ_le_of_lt i.isLt)]
  omega

end Maxwell.Cost.HalfPair
