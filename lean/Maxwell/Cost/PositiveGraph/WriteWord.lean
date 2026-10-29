import Maxwell.Cost.BankArray.WriteCanonical

namespace Maxwell.Cost.BankArray
open Structured
open RationalAccumulator (Blank)

/-- Write any retained binary word through the actual padding and indexed-memory code.
This includes the padded identifiers read directly from the sparse archive. -/
theorem write_word {n : ℕ} (widthBank indexBank baseBank clockBank source : ℕ)
    (hw : 10 ≤ widthBank) (hi : 10 ≤ indexBank) (hb : 10 ≤ baseBank)
    (hc : 10 ≤ clockBank) (hs : 10 ≤ source)
    (hw37 : widthBank ≠ 37) (hi37 : indexBank ≠ 37) (hb37 : baseBank ≠ 37)
    (input : List Bool) (tape : ℕ → Bool) (width index base clock : List Bool)
    (words : Vector (List Bool) n) (i : Fin n) (value : List Bool)
    (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hclock : clock.length = addressValue width) (hpositive : 0 < addressValue width)
    (hfit : value.length ≤ addressValue width)
    (s : Store) (hscratch : Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (hwidthBank : Word s.val widthBank width) (hindexBank : Word s.val indexBank index)
    (hbaseBank : Word s.val baseBank base) (hclockBank : Word s.val clockBank clock)
    (hsource : Word s.val source value)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) words) :
    ∃ cost t, cost ≤ costCap width index base (FixedWidth.bits (addressValue width) value) +
        100 * addressValue width + 100 ∧
      Executes input tape (writeCanonicalCode widthBank indexBank baseBank clockBank source) cost s t ∧
      t.val.memory = MemoryWord.writeBits s.val.memory (addressValue base + i.val * addressValue width)
        (FixedWidth.bits (addressValue width) value) ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width)
        (words.set i (FixedWidth.bits (addressValue width) value)) ∧
      Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 37 ∧ FrameExcept 37 s.val t.val := by
  obtain ⟨pcost, p, hpcost, ep, hpword, hps, hp7, hpcontrol, hpf⟩ :=
    pack_canonical source clockBank hs hc input tape value clock
      (by omega) (by omega) s hscratch h7 h37 hsource hclockBank
  have payload : Word p.val 37 (FixedWidth.bits (addressValue width) value) := by
    simpa only [hclock] using hpword
  obtain ⟨wcost, w, hwcost, ew, hwmem, hwa, hws, hw7, hwf⟩ :=
    write_bank widthBank indexBank baseBank 37 hw hi hb (by omega) input tape
      width index base (FixedWidth.bits (addressValue width) value) words i hwidth hindex
      (FixedWidth.bits_length _ _) p hps
      (word_of_eq (hpf.2.2.2.1 widthBank (Or.inr hw) hw37) hwidthBank)
      (word_of_eq (hpf.2.2.2.1 indexBank (Or.inr hi) hi37) hindexBank)
      (word_of_eq (hpf.2.2.2.1 baseBank (Or.inr hb) hb37) hbaseBank) payload
      (by simpa only [hpcontrol.2.2.2.1] using harray)
  obtain ⟨po, hpword⟩ := payload
  obtain ⟨t, et, ht, ft⟩ := WordCall.clear 37 input tape
    (FixedWidth.bits (addressValue width) value) po w
    ((hwf.2.2.2.1 37 (by omega)).trans hpword)
  have unchanged (j : ℕ) (hj : j ≠ 37) : t.val.tapes j = w.val.tapes j := by simp [ht, hj]
  refine ⟨pcost + (wcost + (6 * (FixedWidth.bits (addressValue width) value).length + 4)), t,
    ?_, ep.seq (ew.seq et), ?_, ?_, ?_, ?_,
    ⟨po + (FixedWidth.bits (addressValue width) value).length, by simp [ht]⟩, ?_⟩
  · simp only [FixedWidth.bits_length]
    omega
  · exact ft.2.2.1.trans (hwmem.trans (congrArg
      (fun memory => MemoryWord.writeBits memory (addressValue base + i.val * addressValue width)
        (FixedWidth.bits (addressValue width) value)) hpcontrol.2.2.2.1))
  · simpa only [ft.2.2.1] using hwa
  · rcases hws with ⟨h0, h1, h2, h3, h5, h6, h8, h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (unchanged 0 (by omega)) h0,
      RationalAccumulator.blank_of_eq (unchanged 1 (by omega)) h1,
      RationalAccumulator.blank_of_eq (unchanged 2 (by omega)) h2,
      RationalAccumulator.blank_of_eq (unchanged 3 (by omega)) h3,
      RationalAccumulator.blank_of_eq (unchanged 5 (by omega)) h5,
      RationalAccumulator.blank_of_eq (unchanged 6 (by omega)) h6,
      RationalAccumulator.blank_of_eq (unchanged 8 (by omega)) h8,
      RationalAccumulator.blank_of_eq (unchanged 9 (by omega)) h9⟩
  · exact RationalAccumulator.blank_of_eq ((unchanged 7 (by omega)).trans hw7) hp7
  · exact ⟨ft.2.1.trans (hwf.1.trans hpf.1),
      ft.2.2.2.1.trans (hwf.2.1.trans hpf.2.1),
      ft.2.2.2.2.1.trans (hwf.2.2.1.trans hpf.2.2.1),
      fun j hj hj37 => (unchanged j hj37).trans
        ((hwf.2.2.2.1 j hj).trans (hpf.2.2.2.1 j hj hj37)),
      fun j hj h24 h25 h26 h27 h28 h29 => (ft.2.2.2.2.2.2 j h26 h27).trans
        ((hwf.2.2.2.2 j hj h24 h25 h26 h27 h28 h29).trans
          (hpf.2.2.2.2 j hj h24 h25 h26 h27 h28 h29))⟩

end Maxwell.Cost.BankArray
