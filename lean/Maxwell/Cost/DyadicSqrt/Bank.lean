import Maxwell.Cost.CalibrationMatrix.Product
import Maxwell.Cost.RationalAccumulator.Add
import Maxwell.Cost.RationalAccumulator.Reset
import Maxwell.Cost.RationalAccumulator.Move
import Maxwell.Cost.RationalCompare.Temporary
import Maxwell.Cost.Structured.CountedShifted

/-! Reusable finite Boolean arithmetic for the integer square-root loop.
Every operand comes from an actual canonical tape word. -/

namespace Maxwell.Cost.DyadicSqrt

open Structured RationalAccumulator

def multiplyCode (source target : ℕ) : Code :=
  .seq (.call (WordTransfer.clone source 1))
    (.seq (CalibrationMatrix.productCode target) (.call (TapeOps.clear 1)))

theorem multiply (source target : ℕ)
    (hs : 30 ≤ source) (hs' : source ≤ 36) (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store,
      cost ≤ 1200 * ((v source).bits.length + (v target).bits.length + 3)^2 ∧
      Executes input tape (multiplyCode source target) cost s t ∧
      Bank t.val (Function.update v target (v source * v target)) ∧
      Scratch t.val 0 ∧ RationalAccumulator.Frame s.val t.val := by
  obtain ⟨a, ea, ba, ra, fa⟩ := clone_to_one source hs hs' input tape v s hbank hready
  obtain ⟨cost, b, cb, eb, bb, rb, fb⟩ :=
    CalibrationMatrix.product target ht ht' input tape v (v source) a ba ra
  obtain ⟨t, et, bt, rt, ft⟩ := clear_one input tape
    (Function.update v target (v source * v target)) (v source) b bb rb
  refine ⟨(15 * (v source).bits.length + 17) + (cost + (6 * (v source).bits.length + 4)),
    t, ?_, ea.seq (eb.seq et), bt, rt, (fa.trans fb).trans ft⟩
  have hx : (v source).bits.length + 1 ≤
      ((v source).bits.length + (v target).bits.length + 3)^2 := by
    exact (show (v source).bits.length + 1 ≤
      (v source).bits.length + (v target).bits.length + 3 by omega).trans
      (Nat.le_self_pow (by decide) _)
  omega

def addCode (source target : ℕ) : Code :=
  .seq (.call (WordTransfer.clone source 1))
    (.seq (RationalAccumulator.addCode target) (.call (TapeOps.clear 1)))

theorem add (source target : ℕ)
    (hs : 30 ≤ source) (hs' : source ≤ 36) (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val 0) :
    ∃ cost, ∃ t : Store,
      cost ≤ 230 * ((v source).bits.length + (v target).bits.length + 4) ∧
      Executes input tape (addCode source target) cost s t ∧
      Bank t.val (Function.update v target (v source + v target)) ∧
      Scratch t.val 0 ∧ RationalAccumulator.Frame s.val t.val := by
  obtain ⟨a, ea, ba, ra, fa⟩ := clone_to_one source hs hs' input tape v s hbank hready
  obtain ⟨cost, b, cb, eb, bb, rb, fb⟩ :=
    add_bank target ht ht' input tape v (v source) a ba ra
  obtain ⟨t, et, bt, rt, ft⟩ := clear_one input tape
    (Function.update v target (v source + v target)) (v source) b bb rb
  refine ⟨(15 * (v source).bits.length + 17) + (cost + (6 * (v source).bits.length + 4)),
    t, by omega, ea.seq (eb.seq et), bt, rt, (fa.trans fb).trans ft⟩

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → (i < 30 ∨ 36 < i) → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 23 → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 35 →
    t.registers i = s.registers i)

theorem Frame.refl (s : BitRAMState) : Frame s s := by simp [Frame]

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  exact RationalCompare.Frame.trans h k

theorem frame_of_bank {s t : BitRAMState} (h : RationalAccumulator.Frame s t) : Frame s t :=
  RationalCompare.frame_of_bank h

end Maxwell.Cost.DyadicSqrt
