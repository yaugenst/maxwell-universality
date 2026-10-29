import Maxwell.Cost.BankArray.Common

namespace Maxwell.Cost.BankArray
open Structured
open RationalAccumulator (Blank)

def readCode (widthBank indexBank baseBank clockBank : ℕ) : Code :=
  .seq (prepare widthBank indexBank baseBank clockBank) (.seq ArrayAccess.readCode cleanup)

/-- A genuine finite array read with persistent metadata banks. The resulting
word is on tape 7; all addressing/arithmetic scratch words are reclaimed. -/
theorem read_executes {n : ℕ} (widthBank indexBank baseBank clockBank : ℕ)
    (hw : 10 ≤ widthBank) (hi : 10 ≤ indexBank) (hb : 10 ≤ baseBank) (hc : 10 ≤ clockBank) (input : List Bool) (tape : ℕ → Bool)
    (width index base clock : List Bool) (words : Vector (List Bool) n) (i : Fin n)
    (wbank ibank bbank cbank outputOrigin : ℤ)
    (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hclock : clock.length = addressValue width) (s : Store)
    (hscratch : Scratch s.val)
    (hwidthBank : s.val.tapes widthBank = BitTape.shifted width wbank)
    (hindexBank : s.val.tapes indexBank = BitTape.shifted index ibank)
    (hclockBank : s.val.tapes clockBank = BitTape.shifted clock cbank)
    (hbaseBank : s.val.tapes baseBank = BitTape.shifted base bbank)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) words)
    (h7 : s.val.tapes 7 = {BitTape.blank with head := outputOrigin}) :
    ∃ cost t, cost ≤ costCap width index base clock ∧ Executes input tape (readCode widthBank indexBank baseBank clockBank) cost s t ∧
      t.val.tapes 7 = BitTape.shiftedEnd (words.get i) outputOrigin ∧
      Scratch t.val ∧ t.val.memory = s.val.memory ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width) words ∧ Frame s.val t.val := by
  rcases hscratch with ⟨⟨ao, h0⟩, ⟨wo, h1⟩, ⟨zo, h2⟩, ⟨yo, h3⟩,
    ⟨io, h5⟩, ⟨co, h6⟩, ⟨bo, h8⟩, ⟨saved, h9⟩⟩
  obtain ⟨p, ep, hp, fp⟩ := prepare_executes widthBank indexBank baseBank clockBank hw hi hb hc
    input tape width index base clock wo io bo co wbank ibank bbank cbank s h1 h5 h8 h6
    hwidthBank hindexBank hbaseBank hclockBank
  have hready : ArrayAccess.Ready p.val width index base ao wo zo yo io bo saved := by
    constructor
    · simpa [hp] using h0
    · simp [hp]
    · simpa [hp] using h2
    · simpa [hp] using h3
    · simp [hp]
    · simp [hp]
    · simpa [hp] using h9
  obtain ⟨rcost, r, address, addressOrigin, hrc, er, hr5, _, hrl, hr6, hr7, hrm, harr, restored, fr⟩ :=
    ArrayAccess.read_executes input tape width index base clock words i ao wo zo yo io bo saved co outputOrigin
      hwidth hindex hclock p hready
      (by simpa [fp.2.2.2.1, addressValue] using harray)
      (by simp [hp]) (by simpa [hp] using h7)
  obtain ⟨widthOrigin, hr1⟩ := restored.width
  obtain ⟨t, et, ht, ft⟩ := cleanup_executes input tape width address clock base
    widthOrigin addressOrigin co bo r hr1 hr5 hr6 restored.base
  have frame : Frame s.val t.val := by
    have control := fp.trans ((DecoderFetch.Control.of_read fr hrm).trans ft)
    refine ⟨control.1, control.2.1, control.2.2.1, ?_, control.2.2.2.2⟩
    intro j hj
    have hj1 : j ≠ 1 := by omega
    have hj5 : j ≠ 5 := by omega
    have hj6 : j ≠ 6 := by omega
    have hj8 : j ≠ 8 := by omega
    simp only [ht, Function.update_apply, hj1, hj5, hj6, hj8, ↓reduceIte]
    rw [fr.2.2.2.1 j (by omega), hp]
    simp [hj1, hj5, hj6, hj8]
  refine ⟨15 * (width.length + index.length + base.length + clock.length) + 68 +
      (rcost + (6 * width.length + 10 * address.length + 10 * clock.length + 6 * base.length + 28)),
    t, ?_, ep.seq (er.seq et), ?_, ?_, ?_, ?_, frame⟩
  · dsimp [costCap]
    omega
  · simpa [ht] using hr7
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨o, ho⟩ := restored.zero
      exact ⟨o, by simpa [ht] using ho⟩
    · exact ⟨widthOrigin + width.length, by simp [ht]⟩
    · obtain ⟨o, ho⟩ := restored.scratch
      exact ⟨o, by simpa [ht] using ho⟩
    · exact ⟨yo + index.length, by simpa [ht] using restored.multiply⟩
    · exact ⟨addressOrigin + address.length, by simp [ht]⟩
    · exact ⟨co + clock.length, by simp [ht]⟩
    · exact ⟨bo + base.length, by simp [ht]⟩
    · exact ⟨saved + width.length, by simpa [ht] using restored.saved⟩
  · exact ft.2.2.2.1.trans (hrm.trans fp.2.2.2.1)
  · simpa [ft.2.2.2.1, addressValue] using harr

end Maxwell.Cost.BankArray
