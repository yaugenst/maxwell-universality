import Maxwell.Cost.BankArray.Read
import Maxwell.Cost.WordMove

namespace Maxwell.Cost.BankArray
open Structured
open RationalAccumulator (Blank)

def readBankCode (widthBank indexBank baseBank clockBank target : ℕ) : Code :=
  .seq (readCode widthBank indexBank baseBank clockBank) (WordCall.moveEnd 7 target)

/-- Store one actual indexed read in a persistent word bank, reclaiming the
sample tape as well as the arithmetic and address workspaces. -/
theorem read_bank {n : ℕ} (widthBank indexBank baseBank clockBank target : ℕ)
    (hw : 10 ≤ widthBank) (hi : 10 ≤ indexBank) (hb : 10 ≤ baseBank)
    (hc : 10 ≤ clockBank) (ht : 10 ≤ target)
    (input : List Bool) (tape : ℕ → Bool) (width index base clock : List Bool)
    (words : Vector (List Bool) n) (i : Fin n)
    (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hclock : clock.length = addressValue width) (s : Store)
    (hscratch : Scratch s.val) (h7 : Blank s.val 7) (hblank : Blank s.val target)
    (hwidthBank : Word s.val widthBank width) (hindexBank : Word s.val indexBank index)
    (hbaseBank : Word s.val baseBank base) (hclockBank : Word s.val clockBank clock)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) words) :
    ∃ cost t, cost ≤ costCap width index base clock + 16 * addressValue width + 17 ∧
      Executes input tape (readBankCode widthBank indexBank baseBank clockBank target) cost s t ∧
      Word t.val target (words.get i) ∧ Scratch t.val ∧ Blank t.val 7 ∧
      t.val.memory = s.val.memory ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width) words ∧
      FrameExcept target s.val t.val := by
  obtain ⟨wbank, hwidthBank⟩ := hwidthBank
  obtain ⟨ibank, hindexBank⟩ := hindexBank
  obtain ⟨bbank, hbaseBank⟩ := hbaseBank
  obtain ⟨cbank, hclockBank⟩ := hclockBank
  obtain ⟨outputOrigin, h7⟩ := h7
  obtain ⟨targetOrigin, hblank⟩ := hblank
  obtain ⟨rcost, r, hrc, er, hr7, hrs, hrm, hra, hrf⟩ :=
    read_executes widthBank indexBank baseBank clockBank hw hi hb hc input tape width index base clock
      words i wbank ibank bbank cbank outputOrigin hwidth hindex hclock s hscratch
      hwidthBank hindexBank hclockBank hbaseBank harray h7
  have hrt : r.val.tapes target = {BitTape.blank with head := targetOrigin} :=
    (hrf.2.2.2.1 target (by omega)).trans hblank
  obtain ⟨t, et, htapes, ft⟩ := WordCall.move_end 7 target (by omega) input tape (words.get i)
    outputOrigin targetOrigin r hr7 hrt
  have hlen : (words.get i).length = addressValue width := harray.length i
  refine ⟨rcost + (16 * (words.get i).length + 17), t, by omega, er.seq et,
    ⟨targetOrigin, by simp [htapes]⟩, ?_, ⟨outputOrigin + (words.get i).length, ?_⟩,
    ft.2.2.1.trans hrm, ?_, ?_⟩
  · rcases hrs with ⟨h0, h1, h2, h3, h5, h6, h8, h9⟩
    have unchanged (j : ℕ) (hj : j < 10) (hj7 : j ≠ 7) : t.val.tapes j = r.val.tapes j := by
      simp [htapes, hj7, show j ≠ target by omega]
    exact ⟨RationalAccumulator.blank_of_eq (unchanged 0 (by omega) (by omega)) h0,
      RationalAccumulator.blank_of_eq (unchanged 1 (by omega) (by omega)) h1,
      RationalAccumulator.blank_of_eq (unchanged 2 (by omega) (by omega)) h2,
      RationalAccumulator.blank_of_eq (unchanged 3 (by omega) (by omega)) h3,
      RationalAccumulator.blank_of_eq (unchanged 5 (by omega) (by omega)) h5,
      RationalAccumulator.blank_of_eq (unchanged 6 (by omega) (by omega)) h6,
      RationalAccumulator.blank_of_eq (unchanged 8 (by omega) (by omega)) h8,
      RationalAccumulator.blank_of_eq (unchanged 9 (by omega) (by omega)) h9⟩
  · simp [htapes, show 7 ≠ target by omega]
  · simpa [ft.2.2.1] using hra
  · refine ⟨ft.2.1.trans hrf.1, ft.2.2.2.1.trans hrf.2.1,
      ft.2.2.2.2.1.trans hrf.2.2.1, ?_, ?_⟩
    · intro j hj hjt
      rw [htapes]
      simp only [Function.update_apply, hjt, show j ≠ 7 by omega, ↓reduceIte]
      exact hrf.2.2.2.1 j hj
    · intro j hj h24 h25 h26 h27 h28 h29
      exact (ft.2.2.2.2.2.2 j h24 h25 h26 h27).trans
        (hrf.2.2.2.2 j hj h24 h25 h26 h27 h28 h29)

end Maxwell.Cost.BankArray
