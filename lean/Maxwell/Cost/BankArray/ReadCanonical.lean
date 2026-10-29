import Maxwell.Cost.BankArray.ReadBank
import Maxwell.Cost.NormalizeWord

namespace Maxwell.Cost.BankArray
open Structured
open RationalAccumulator (Blank)

def readCanonicalCode (widthBank indexBank baseBank clockBank target : ℕ) : Code :=
  .seq (readBankCode widthBank indexBank baseBank clockBank target) (.call (NormalizeWord.program target))

/-- An indexed array read followed by actual high-zero trimming. The result
uses the canonical natural-word convention of the rational arithmetic bank. -/
theorem read_canonical {n : ℕ} (widthBank indexBank baseBank clockBank target : ℕ)
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
    ∃ cost t, cost ≤ costCap width index base clock + 32 * addressValue width + 35 ∧
      Executes input tape (readCanonicalCode widthBank indexBank baseBank clockBank target) cost s t ∧
      RationalAccumulator.Word t.val target (addressValue (words.get i)) ∧
      Scratch t.val ∧ Blank t.val 7 ∧ t.val.memory = s.val.memory ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width) words ∧
      FrameExcept target s.val t.val := by
  obtain ⟨rcost, r, hrc, er, hrword, hrs, hr7, hrm, hra, hrf⟩ :=
    read_bank widthBank indexBank baseBank clockBank target hw hi hb hc ht input tape width index base clock
      words i hwidth hindex hclock s hscratch h7 hblank hwidthBank hindexBank hbaseBank hclockBank harray
  obtain ⟨origin, horigin⟩ := hrword
  obtain ⟨ncost, t, hnc, en, hp, htword, _, htf⟩ := NormalizeWord.simulation target origin input tape
    (words.get i) r.val r.property horigin
  have ne : Executes input tape (.call (NormalizeWord.program target)) (ncost + 1) r (Store.ofState t) :=
    .call _ r t _ en (by
      simp [NormalizeWord.program, hp, ScanForward.program, TapeOps.trim, Rewind.program,
        BitRAMInstruction.relocate])
  have hlen := harray.length i
  refine ⟨rcost + (ncost + 1), Store.ofState t, by omega, er.seq ne, ⟨origin, htword⟩,
    ?_, RationalAccumulator.blank_of_eq (htf.2.2.2.2.2.1 7 (by omega)) hr7,
    htf.2.2.1.trans hrm, by simpa [Store.ofState, htf.2.2.1] using hra, ?_⟩
  · rcases hrs with ⟨h0, h1, h2, h3, h5, h6, h8, h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (htf.2.2.2.2.2.1 0 (by omega)) h0,
      RationalAccumulator.blank_of_eq (htf.2.2.2.2.2.1 1 (by omega)) h1,
      RationalAccumulator.blank_of_eq (htf.2.2.2.2.2.1 2 (by omega)) h2,
      RationalAccumulator.blank_of_eq (htf.2.2.2.2.2.1 3 (by omega)) h3,
      RationalAccumulator.blank_of_eq (htf.2.2.2.2.2.1 5 (by omega)) h5,
      RationalAccumulator.blank_of_eq (htf.2.2.2.2.2.1 6 (by omega)) h6,
      RationalAccumulator.blank_of_eq (htf.2.2.2.2.2.1 8 (by omega)) h8,
      RationalAccumulator.blank_of_eq (htf.2.2.2.2.2.1 9 (by omega)) h9⟩
  · exact ⟨htf.2.1.trans hrf.1, htf.2.2.2.1.trans hrf.2.1, htf.2.2.2.2.1.trans hrf.2.2.1,
      fun j hj hjt => (htf.2.2.2.2.2.1 j hjt).trans (hrf.2.2.2.1 j hj hjt),
      fun j hj h24 h25 h26 h27 h28 h29 =>
        (htf.2.2.2.2.2.2 j h24 h25 h26 h27).trans (hrf.2.2.2.2 j hj h24 h25 h26 h27 h28 h29)⟩

end Maxwell.Cost.BankArray
