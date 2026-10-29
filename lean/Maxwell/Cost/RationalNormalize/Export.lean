import Maxwell.Cost.RationalNormalize.Bank
import Maxwell.Cost.CalibrationMatrix.Term

namespace Maxwell.Cost.RationalNormalize

open Structured RationalAccumulator

def clearAllCode : Code := .seq CalibrationMatrix.clearOperandsCode
  (.seq resetCode (.call (TapeOps.clear 36)))

theorem clear_all (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (W : ℕ)
    (hv : DyadicSqrt.Width v W) (s : Store) (hb : Bank s.val v) (hr : Scratch s.val 0) :
    ∃ cost, ∃ t : Store, cost ≤ 42*W+32 ∧ Executes input tape clearAllCode cost s t ∧
      Bank t.val (fun _ => 0) ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨a, ea, ba, ra, fa⟩ := CalibrationMatrix.clear_operands input tape v s hb hr
  obtain ⟨b, eb, bb, rb, fb⟩ := reset input tape (CalibrationMatrix.clearOperands v) a ba ra
  obtain ⟨t, et, bt, rt, ft⟩ := clear_bank 36 (by decide) (by decide) input tape
    (resetBank (CalibrationMatrix.clearOperands v)) 0 b bb rb
  refine ⟨_, t, ?_, ea.seq (eb.seq et), ?_, rt,
    frame_of_bank ((fa.trans fb).trans ft)⟩
  · have h30 := hv 30 (by decide) (by decide)
    have h31 := hv 31 (by decide) (by decide)
    have h32 := hv 32 (by decide) (by decide)
    have h33 := hv 33 (by decide) (by decide)
    have h34 := hv 34 (by decide) (by decide)
    have h35 := hv 35 (by decide) (by decide)
    have h36 := hv 36 (by decide) (by decide)
    simp only [resetBank, CalibrationMatrix.clearOperands,
      Function.update_of_ne (by decide : (36:ℕ) ≠ 30),
      Function.update_of_ne (by decide : (36:ℕ) ≠ 31),
      Function.update_of_ne (by decide : (36:ℕ) ≠ 32),
      Function.update_of_ne (by decide : (36:ℕ) ≠ 33),
      Function.update_of_ne (by decide : (36:ℕ) ≠ 34),
      Function.update_of_ne (by decide : (36:ℕ) ≠ 35)]
    norm_num [Function.update_apply]
    omega
  · intro i hi hi'
    have hh := bt i hi hi'
    interval_cases i <;> simpa [resetBank, CalibrationMatrix.clearOperands] using hh

def ExportFrame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → (i < 30 ∨ 36 < i) → i ≠ 126 → i ≠ 153 → t.tapes i = s.tapes i) ∧
  (∀ i, 36 ≤ i → t.registers i = s.registers i)

def exportCode : Code := .seq (.call (WordTransfer.clone 33 126))
  (.seq (.call (WordTransfer.clone 32 153)) clearAllCode)

/-- Emit the common numerator multiplier and denominator as actual
integer words, then restore the entire arithmetic bank for the array pass. -/
theorem export_executes (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (W : ℕ)
    (hv : DyadicSqrt.Width v W) (s : Store) (hb : Bank s.val v) (hr : Scratch s.val 0)
    (h126 : Blank s.val 126) (h153 : Blank s.val 153) :
    ∃ cost, ∃ t : Store, cost ≤ 100*(W+1) ∧ Executes input tape exportCode cost s t ∧
      Word t.val 126 (v 33) ∧ Word t.val 153 (v 32) ∧ Bank t.val (fun _ => 0) ∧
      Scratch t.val 0 ∧ ExportFrame s.val t.val := by
  obtain ⟨o33, h33⟩ := hb 33 (by decide) (by decide)
  obtain ⟨o126, h126⟩ := h126
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clone 33 126 (by decide) input tape
    (v 33).bits o33 o126 s h33 h126
  have keepa (i : ℕ) (hi : i ≠ 126) : a.val.tapes i = s.val.tapes i := by simp [ha, hi]
  obtain ⟨o32, h32⟩ := word_of_eq (keepa 32 (by decide)) (hb 32 (by decide) (by decide))
  obtain ⟨o153, ha153⟩ := blank_of_eq (keepa 153 (by decide)) h153
  obtain ⟨b, eb, hbTapes, fb⟩ := WordCall.clone 32 153 (by decide) input tape
    (v 32).bits o32 o153 a h32 ha153
  have keepb (i : ℕ) (hi : i ≠ 126) (hj : i ≠ 153) : b.val.tapes i = s.val.tapes i := by
    simp [hbTapes, ha, hi, hj]
  have bb : Bank b.val v := fun i hi hi' => word_of_eq (keepb i (by omega) (by omega)) (hb i hi hi')
  have rb : Scratch b.val 0 :=
    ⟨blank_of_eq (keepb 0 (by decide) (by decide)) hr.1,
      word_of_eq (keepb 1 (by decide) (by decide)) hr.2.1,
      blank_of_eq (keepb 2 (by decide) (by decide)) hr.2.2.1,
      blank_of_eq (keepb 3 (by decide) (by decide)) hr.2.2.2⟩
  obtain ⟨c, t, hc, et, bt, rt, ft⟩ := clear_all input tape v W hv b bb rb
  refine ⟨15*(v 33).bits.length+17+(15*(v 32).bits.length+17+c), t, ?_,
    ea.seq (eb.seq et), ?_, ?_, bt, rt, ?_⟩
  · have h32b := hv 32 (by decide) (by decide)
    have h33b := hv 33 (by decide) (by decide)
    omega
  · exact word_of_eq (ft.2.2.2.2.2.1 126 (by decide)) ⟨o126, by simp [hbTapes, ha]⟩
  · exact word_of_eq (ft.2.2.2.2.2.1 153 (by decide)) ⟨o153, by simp [hbTapes]⟩
  · refine ⟨ft.1.trans (fb.1.trans fa.1), ft.2.1.trans (fb.2.1.trans fa.2.1),
      ft.2.2.1.trans (fb.2.2.1.trans fa.2.2.1),
      ft.2.2.2.1.trans (fb.2.2.2.1.trans fa.2.2.2.1),
      ft.2.2.2.2.1.trans (fb.2.2.2.2.1.trans fa.2.2.2.2.1), ?_, ?_⟩
    · intro i hi hj hk hl
      exact (ft.2.2.2.2.2.1 i (by omega)).trans (keepb i hk hl)
    · intro i hi
      exact (ft.2.2.2.2.2.2 i hi).trans
        ((fb.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)).trans
          (fa.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)))

end Maxwell.Cost.RationalNormalize
