import Maxwell.Cost.CalibrationMatrix.EqualWord

namespace Maxwell.Cost.CalibrationMatrix

open Structured BankArray

/-- Saved comparison results occupy one contiguous register interval. -/
structure TestWordsFrame (first count : ℕ) (s t : BitRAMState) : Prop where
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, 3 ≤ i → t.tapes i = s.tapes i
  registers : ∀ i, 100 ≤ i → (i < first ∨ first+count ≤ i) →
    t.registers i = s.registers i

theorem TestWordsFrame.word {first count : ℕ} {s t : BitRAMState}
    (h : TestWordsFrame first count s t) {i : ℕ} (hi : 3 ≤ i) {word : List Bool}
    (hw : Word s i word) : Word t i word := word_of_eq (h.tapes i hi) hw

private def saveTestCode (dst : ℕ) : Code :=
  .seq (.atom (.bitNot dst 2)) (.atom (.bitNot dst dst))

private def saveTestStore (dst : ℕ) (s : Store) : Store :=
  let a := Store.ofState (s.val.setRegister dst (!s.val.registers 2))
  Store.ofState (a.val.setRegister dst (!a.val.registers dst))

private theorem save_test (dst : ℕ) (input : List Bool) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (saveTestCode dst) 4 s (saveTestStore dst s) :=
  (Executes.bitNot input tape s dst 2).seq
    (Executes.bitNot input tape (Store.ofState (s.val.setRegister dst (!s.val.registers 2))) dst dst)

private theorem saved_registers (dst : ℕ) (s : Store) :
    (saveTestStore dst s).val.registers = Function.update s.val.registers dst (s.val.registers 2) := by
  simp [saveTestStore, Store.ofState, BitRAMState.setRegister]

/-- The number and addresses of comparisons are compile-time parameters;
the word contents are read by the actual equality programs. -/
def testWordsFromCode : (count first : ℕ) → (Fin count → ℕ) → (Fin count → ℕ) → Code
  | 0, _, _, _ => .skip
  | count+1, first, left, right => .seq (equalWordCode (left 0) (right 0))
      (.seq (saveTestCode first)
        (testWordsFromCode count (first+1) (fun i => left i.succ) (fun i => right i.succ)))

/-- Each equality result survives every subsequent comparison and is stored
in its own register. All input words and the arithmetic scratch are preserved. -/
theorem test_words_from (count first width : ℕ) (hfirst : 100 ≤ first)
    (left right : Fin count → ℕ) (hl : ∀ i, 10 ≤ left i) (hr : ∀ i, 10 ≤ right i)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : Fin count → List Bool)
    (hxl : ∀ i, (xs i).length ≤ width) (hyl : ∀ i, (xs i).length = (ys i).length)
    (s : Store) (hxs : ∀ i, Word s.val (left i) (xs i))
    (hys : ∀ i, Word s.val (right i) (ys i)) (hs : Scratch s.val) :
    ∃ cost t, cost ≤ count*(160*width+156)+1 ∧
      Executes input tape (testWordsFromCode count first left right) cost s t ∧
      (∀ i, t.val.registers (first+i.val) = true ↔ addressValue (xs i) = addressValue (ys i)) ∧
      Scratch t.val ∧ TestWordsFrame first count s.val t.val := by
  induction count generalizing first s with
  | zero =>
    exact ⟨1, s, by simp, .skip s, fun i => Fin.elim0 i, hs,
      ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩⟩
  | succ count ih =>
    obtain ⟨cost, a, hc, ea, ha2, _, _, has, ham, hak, haf⟩ :=
      equal_word_bank (left 0) (right 0) (hl 0) (hr 0) input tape (xs 0) (ys 0)
        (hyl 0) s (hxs 0) (hys 0) hs
    let b := saveTestStore first a
    have eb : Executes input tape (saveTestCode first) 4 a b := save_test first input tape a
    have bk (i : ℕ) (hi : 3 ≤ i) : b.val.tapes i = s.val.tapes i := hak i hi
    obtain ⟨tc, t, htc, et, htbits, hts, htf⟩ :=
      ih (first+1) (by omega) (fun i => left i.succ) (fun i => right i.succ)
        (fun i => hl i.succ) (fun i => hr i.succ) (fun i => xs i.succ) (fun i => ys i.succ)
        (fun i => hxl i.succ) (fun i => hyl i.succ) b
        (fun i => word_of_eq (bk (left i.succ) (by have h := hl i.succ; omega)) (hxs i.succ))
        (fun i => word_of_eq (bk (right i.succ) (by have h := hr i.succ; omega)) (hys i.succ)) has
    refine ⟨cost+(4+tc), t, ?_, ea.seq (eb.seq et), ?_, hts,
      ⟨htf.memory.trans ham, htf.inputHead.trans haf.1,
        htf.randomCursor.trans haf.2.1, htf.output.trans haf.2.2.1,
        fun i hi => (htf.tapes i hi).trans (bk i hi), ?_⟩⟩
    · have hw := hxl 0
      rw [Nat.succ_mul]
      omega
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · have hp := htf.registers first hfirst (Or.inl (by omega))
        simpa [hp, b, saved_registers] using ha2
      · simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1] using htbits j
    · intro i hi hout
      have hit : i ≠ first := by omega
      have htreg := htf.registers i hi (by omega)
      have hareg := haf.2.2.2.2 i (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
      rw [htreg]
      change (saveTestStore first a).val.registers i = s.val.registers i
      rw [saved_registers, Function.update_of_ne hit, hareg]

def testWordsCode (count : ℕ) (left right : Fin count → ℕ) : Code :=
  testWordsFromCode count 200 left right

theorem test_words (count width : ℕ) (left right : Fin count → ℕ)
    (hl : ∀ i, 10 ≤ left i) (hr : ∀ i, 10 ≤ right i)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : Fin count → List Bool)
    (hxl : ∀ i, (xs i).length ≤ width) (hyl : ∀ i, (xs i).length = (ys i).length)
    (s : Store) (hxs : ∀ i, Word s.val (left i) (xs i))
    (hys : ∀ i, Word s.val (right i) (ys i)) (hs : Scratch s.val) :
    ∃ cost t, cost ≤ count*(160*width+156)+1 ∧
      Executes input tape (testWordsCode count left right) cost s t ∧
      (∀ i, t.val.registers (200+i.val) = true ↔ addressValue (xs i) = addressValue (ys i)) ∧
      Scratch t.val ∧ TestWordsFrame 200 count s.val t.val :=
  test_words_from count 200 width (by decide) left right hl hr input tape xs ys hxl hyl s hxs hys hs

def twelveWordTestsCode (left right : Fin 12 → ℕ) : Code := testWordsCode 12 left right

/-- Three direction tests and nine coordinate tests, saved at 200 through 211. -/
theorem twelve_word_tests (width : ℕ) (left right : Fin 12 → ℕ)
    (hl : ∀ i, 10 ≤ left i) (hr : ∀ i, 10 ≤ right i)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : Fin 12 → List Bool)
    (hxl : ∀ i, (xs i).length ≤ width) (hyl : ∀ i, (xs i).length = (ys i).length)
    (s : Store) (hxs : ∀ i, Word s.val (left i) (xs i))
    (hys : ∀ i, Word s.val (right i) (ys i)) (hs : Scratch s.val) :
    ∃ cost t, cost ≤ 12*(160*width+156)+1 ∧
      Executes input tape (twelveWordTestsCode left right) cost s t ∧
      (∀ i, t.val.registers (200+i.val) = true ↔ addressValue (xs i) = addressValue (ys i)) ∧
      Scratch t.val ∧ TestWordsFrame 200 12 s.val t.val :=
  test_words 12 width left right hl hr input tape xs ys hxl hyl s hxs hys hs

end Maxwell.Cost.CalibrationMatrix
