import Maxwell.Cost.CalibrationMatrix.TestInputs

namespace Maxwell.Cost.CalibrationMatrix.TestEntry
open Structured BankArray WordSchedule TestInputs
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def result (raw : Fin 7 → List Bool) (i : Fin 12) : Bool :=
  decide (addressValue (leftSource raw i) = addressValue (rightSource raw i))

def rowValues (raw : Fin 7 → List Bool) (j : Direction) : ℕ :=
  addressValue (raw (Fin.ofNat 7 (j.val+1)))

def columnValues (raw : Fin 7 → List Bool) (j : Direction) : ℕ :=
  addressValue (raw (Fin.ofNat 7 (j.val+4)))

theorem result_direction (raw : Fin 7 → List Bool) (rd : Direction)
    (hrd : addressValue (raw 0) = rd.val) (j : Direction) :
    result raw ⟨j.val, by have := j.isLt; omega⟩ = directionTests rd j := by
  simp [result, leftSource, rightSource, j.isLt, hrd,
    directionTests, Fin.ext_iff]

theorem result_coordinate (raw : Fin 7 → List Bool) (j delta : Fin 3) :
    result raw ⟨3+3*j.val+delta.val, by have := j.isLt; have := delta.isLt; omega⟩ =
      coordinateTests (rowValues raw) (columnValues raw) j delta := by
  fin_cases j <;> fin_cases delta <;>
    simp [result, leftSource, rightSource, rowValues, columnValues,
      coordinateTests, coordinateTest, Increment.bits_value]

def code : Code := .seq (WordSchedule.code 101 plan) (twelveWordTestsCode left right)

structure Frame (s t : Store) : Prop where
  memory : t.val.memory = s.val.memory
  inputHead : t.val.inputHead = s.val.inputHead
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  tapes : ∀ i, 3 ≤ i → i ∉ WordSchedule.changes plan → t.val.tapes i = s.val.tapes i
  registers : ∀ i, 100 ≤ i → (i < 200 ∨ 212 ≤ i) → t.val.registers i = s.val.registers i

/-- The actual fixed preparation and comparison programs populate all twelve
Boolean registers used by the sixteen stencil terms and the diagonal test. -/
theorem executes (width : ℕ) (clockWord : List Bool) (raw : Fin 7 → List Bool)
    (hwidth : 2 ≤ width) (hclock : clockWord.length = width)
    (hraw : ∀ i, (raw i).length+1 ≤ width) (rd : Direction)
    (hrd : addressValue (raw 0) = rd.val) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (hb : Banks domain s (initial clockWord raw)) (hs : Scratch s.val) :
    ∃ cost t, cost ≤ 3500*(width+1) ∧ Executes input tape code cost s t ∧
      (∀ j, t.val.registers (200+j.val) = directionTests rd j) ∧
      (∀ j delta, t.val.registers (203+3*j.val+delta.val) =
        coordinateTests (rowValues raw) (columnValues raw) j delta) ∧
      Banks domain t (prepared width clockWord raw) ∧ Scratch t.val ∧ Frame s t := by
  obtain ⟨a, m, hca, ea, hbm, hsm, hf⟩ := prepare width clockWord raw hwidth hclock
    hraw input tape s hb hs
  have hl : ∀ i, left i ∈ domain := by decide
  have hr : ∀ i, right i ∈ domain := by decide
  let xs : Fin 12 → List Bool := fun i => FixedWidth.bits width (leftSource raw i)
  let ys : Fin 12 → List Bool := fun i => FixedWidth.bits width (rightSource raw i)
  have hxs (i : Fin 12) : Word m.val (left i) (xs i) := by
    simpa only [prepared_left] using hbm (left i) (hl i)
  have hys (i : Fin 12) : Word m.val (right i) (ys i) := by
    simpa only [prepared_right] using hbm (right i) (hr i)
  obtain ⟨b, t, hcb, eb, hout, hst, hg⟩ := twelve_word_tests width left right
    (by decide) (by decide) input tape xs ys (by intro i; simp [xs])
    (by intro i; simp [xs,ys]) m hxs hys hsm
  have hresult (i : Fin 12) : t.val.registers (200+i.val) = result raw i := by
    apply Bool.eq_iff_iff.mpr
    rw [hout i]
    simp only [result, decide_eq_true_eq, xs, ys,
      FixedWidth.bits_value width _ (source_lengths width raw hwidth hraw i).1,
      FixedWidth.bits_value width _ (source_lengths width raw hwidth hraw i).2]
  refine ⟨a+b,t,by nlinarith,ea.seq eb,?_,?_,?_,hst,?_⟩
  · intro j
    exact (hresult ⟨j.val, by have := j.isLt; omega⟩).trans (result_direction raw rd hrd j)
  · intro j delta
    have h := (hresult ⟨3+3*j.val+delta.val, by have := j.isLt; have := delta.isLt; omega⟩).trans
      (result_coordinate raw j delta)
    have he : 200+(3+3*j.val+delta.val) = 203+3*j.val+delta.val := by omega
    simpa only [Fin.val_mk, he] using h
  · intro i hi
    have high : ∀ i ∈ domain, 100 ≤ i := by decide
    exact hg.word (by have := high i hi; omega) (hbm i hi)
  · exact ⟨hg.memory.trans hf.memory, hg.inputHead.trans hf.inputHead,
      hg.randomCursor.trans hf.randomCursor, hg.output.trans hf.output,
      fun i hi hout => (hg.tapes i (by omega)).trans (hf.tapes i hout),
      fun i hi hout => (hg.registers i hi hout).trans (hf.registers i hi)⟩

end Maxwell.Cost.CalibrationMatrix.TestEntry
