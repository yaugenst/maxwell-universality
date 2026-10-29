import Maxwell.Cost.CalibrationMatrix.EraseWords
import Maxwell.Cost.CalibrationMatrix.TestInputs

namespace Maxwell.Cost.CalibrationMatrix.GeneratedCleanup
open Structured BankArray WordSchedule
open RationalAccumulator (Blank)
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

def banks : List ℕ := [150,151,152,153,170,171,172,173,161,162,163,181,182,183,
  221,222,190,191,192,193,194,195,196,201,202,203,204,205,206,210,211,212,220]

theorem prepared_length (width : ℕ) (clockWord : List Bool) (raw : Fin 7 → List Bool)
    (hwidth : 2 ≤ width) (hraw : ∀ i, (raw i).length+1 ≤ width)
    (i : ℕ) (hi : i ∈ TestInputs.domain) (hclock : i ≠ 101) :
    (TestInputs.prepared width clockWord raw i).length ≤ width := by
  have hr (j : Fin 7) : (raw j).length ≤ width := by have := hraw j; omega
  have hs (j : Fin 7) : (Increment.bits (raw j)).length ≤ width :=
    (Increment.bits_length_le _).trans (hraw j)
  have hinc0 : Increment.bits [] = [true] := rfl
  have hinc1 : Increment.bits [true] = [false,true] := rfl
  fin_cases hi <;> simp [TestInputs.prepared, WordSchedule.run, TestInputs.plan,
    Op.apply,Op.result,Op.target,TestInputs.initial,hr,hs,hinc0,hinc1] <;> omega

def code : Code := EraseWords.code banks

/-- All operand and comparison banks are cleared by one fixed sequence of
actual tape-erasure programs, making entry generation reusable. -/
theorem executes (width : ℕ) (clockWord direction : List Bool) (raw : Fin 7 → List Bool)
    (hwidth : 2 ≤ width) (hraw : ∀ i, (raw i).length+1 ≤ width)
    (hdirection : direction.length ≤ width) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : Banks TestInputs.domain s (TestInputs.prepared width clockWord raw))
    (hdir : Word s.val 170 direction) :
    ∃ cost t, cost ≤ 33*(6*width+4)+1 ∧ Executes input tape code cost s t ∧
      (∀ i ∈ banks, Blank t.val i) ∧ BinaryPrecision.Frame banks.toFinset s.val t.val := by
  let words := Function.update (TestInputs.prepared width clockWord raw) 170 direction
  have membership : ∀ i ∈ banks, i = 170 ∨ (i ∈ TestInputs.domain ∧ i ≠ 101) := by decide
  have hlen (i : ℕ) (hi : i ∈ banks) : (words i).length ≤ width := by
    rcases membership i hi with rfl | hm
    · simpa [words] using hdirection
    · by_cases h170 : i = 170
      · simpa [words,h170] using hdirection
      · simpa [words,h170] using prepared_length width clockWord raw hwidth hraw i hm.1 hm.2
  have hw (i : ℕ) (hi : i ∈ banks) : Word s.val i (words i) := by
    rcases membership i hi with rfl | hm
    · simpa [words] using hdir
    · by_cases h170 : i = 170
      · simpa [words,h170] using hdir
      · simpa [words,h170] using hb i hm.1
  exact EraseWords.executes banks width words hlen input tape s hw

end Maxwell.Cost.CalibrationMatrix.GeneratedCleanup
