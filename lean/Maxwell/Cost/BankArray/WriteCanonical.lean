import Maxwell.Cost.BankArray.Write
import Maxwell.Cost.FixedWidth
import Maxwell.Cost.PadWord
import Maxwell.Cost.WordMove

/-! Store a canonical natural word in a fixed-width memory array. Every
padding, rewind, memory write, and temporary-tape cleanup is actual code. -/
namespace Maxwell.Cost.BankArray
open Structured
open RationalAccumulator (Blank)

private theorem fixedWidth_padWord (width : ℕ) (xs : List Bool) :
    FixedWidth.bits width (PadWord.bits xs) = FixedWidth.bits width xs := by
  cases xs with
  | nil => cases width <;> rfl
  | cons b xs => rfl

private theorem padWord_length_le (xs : List Bool) (width : ℕ)
    (hw : 0 < width) (hx : xs.length ≤ width) : (PadWord.bits xs).length ≤ width := by
  cases xs with
  | nil => simp only [PadWord.bits, List.length_singleton]; omega
  | cons b xs => simpa [PadWord.bits] using hx

def packCanonicalCode (source clockBank : ℕ) : Code :=
  .seq (.call (WordTransfer.clone source 1))
  (.seq (.call (PadWord.program 1))
  (.seq (.call (WordTransfer.clone clockBank 6))
  (.seq (.call (FixedWidth.program 1 6 7))
  (.seq (.call (RewindOvershoot.program 1))
  (.seq (.call (TapeOps.clear 1))
  (.seq (WordCall.eraseEnd 6) (WordCall.moveEnd 7 37)))))))

/-- Actual fixed-width packing into temporary bank37, restoring scratch. -/
theorem pack_canonical (source clockBank : ℕ) (hs : 10 ≤ source) (hc : 10 ≤ clockBank)
    (input : List Bool) (tape : ℕ → Bool) (xs clock : List Bool)
    (hclock : 0 < clock.length) (hfit : xs.length ≤ clock.length)
    (s : Store) (hscratch : Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (hsource : Word s.val source xs) (hclockBank : Word s.val clockBank clock) :
    ∃ cost t, cost ≤ 80 * clock.length + 90 ∧
      Executes input tape (packCanonicalCode source clockBank) cost s t ∧
      Word t.val 37 (FixedWidth.bits clock.length xs) ∧
      Scratch t.val ∧ Blank t.val 7 ∧ Control s.val t.val ∧ FrameExcept 37 s.val t.val := by
  obtain ⟨so, hsource⟩ := hsource
  obtain ⟨co, hclockBank⟩ := hclockBank
  obtain ⟨xo, h1⟩ := hscratch.2.1
  obtain ⟨wo, h6⟩ := hscratch.2.2.2.2.2.1
  obtain ⟨yo, h7⟩ := h7
  obtain ⟨po, h37⟩ := h37
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clone source 1 (by omega) input tape xs so xo s hsource h1
  obtain ⟨pcost, hpcost, ep, hp1, fp⟩ := PadWord.simulation 1 xo input tape xs a.val a.property
    (by simp [ha])
  let p := Store.ofState (PadWord.finish 1 a.val xs)
  have eP : Executes input tape (.call (PadWord.program 1)) (pcost + 1) a p :=
    .call _ a _ _ ep (by simp [PadWord.program, PadWord.finish])
  obtain ⟨b, eb, hb, fb⟩ := WordCall.clone clockBank 6 (by omega) input tape clock co wo p
    (by
      exact (fp.2.2.2.2.2.1 clockBank (by omega) (by omega)).trans
        (by simpa [ha, show clockBank ≠ 1 by omega] using hclockBank))
    (by exact (fp.2.2.2.2.2.1 6 (by omega) (by omega)).trans (by simpa [ha] using h6))
  obtain ⟨fstate, ef, fpc, f1, f6, f7, ff⟩ := FixedWidth.simulation 1 6 7 (by omega) (by omega) (by omega)
    input tape clock (PadWord.bits xs) xo wo yo b.val b.property
    (by simp [hb]) (by simpa [hb, p, Store.ofState] using hp1)
    (by
      rw [hb]
      simp only [Function.update_of_ne (show (7:ℕ) ≠ 6 by omega)]
      exact (fp.2.2.2.2.2.1 7 (by omega) (by omega)).trans (by simpa [ha] using h7))
  let f := Store.ofState fstate
  have eF : Executes input tape (.call (FixedWidth.program 1 6 7)) (10 * clock.length + 4) b f :=
    .call _ b fstate _ ef (by simp [FixedWidth.program, fpc])
  have fit := padWord_length_le xs clock.length hclock hfit
  have er := WordTransfer.rewind_overshoot_shifted 1 xo input tape (PadWord.bits xs) clock.length
    (PadWord.nonempty xs) fit f.val f.property f1
  let r := Store.ofState (RewindOvershoot.finish 1 xo f.val)
  have eR : Executes input tape (.call (RewindOvershoot.program 1)) (4 * clock.length + 7) f r :=
    .call _ f _ _ er.1 (by simp [RewindOvershoot.program, RewindOvershoot.finish,
      RewindOvershoot.preamble, BitRAM.link, Rewind.program])
  obtain ⟨c, ec, htC, fc⟩ := WordCall.clear 1 input tape (PadWord.bits xs) xo r er.2
  obtain ⟨d, ed, hd, fd⟩ := WordCall.erase_end 6 input tape clock wo c
    (by simpa [htC, r, f, Store.ofState, RewindOvershoot.finish, Rewind.finishAt] using f6)
  obtain ⟨t, et, ht, ft⟩ := WordCall.move_end 7 37 (by omega) input tape
    (FixedWidth.bits clock.length (PadWord.bits xs)) yo po d
    (by simpa [hd, htC, r, f, Store.ofState, RewindOvershoot.finish, Rewind.finishAt] using f7)
    (by
      rw [hd, htC]
      simp only [Function.update_of_ne (show (37:ℕ) ≠ 6 by omega),
        Function.update_of_ne (show (37:ℕ) ≠ 1 by omega)]
      change f.val.tapes 37 = _
      exact (ff.2.2.2.2.2.1 37 (by omega) (by omega) (by omega)).trans
        (by
          rw [hb]
          simp only [Function.update_of_ne (show (37:ℕ) ≠ 6 by omega)]
          exact (fp.2.2.2.2.2.1 37 (by omega) (by omega)).trans (by simpa [ha] using h37)))
  have fcontrol : Control b.val f.val := by
    rcases ff with ⟨_, hinput, hmemory, hrandom, houtput, _, hregisters⟩
    exact ⟨hinput, hrandom, houtput, hmemory,
      fun i _ _ _ h26 h27 h28 h29 => hregisters i h26 h27 h28 h29⟩
  have rcontrol : Control f.val r.val :=
    DecoderFetch.Control.of_transfer (WordTransfer.frame_rewind 1 1 1 (Or.inl rfl) xo f.val)
  have control : Control s.val t.val :=
    (DecoderFetch.Control.of_transfer fa).trans ((DecoderFetch.Control.of_clear fp).trans
      ((DecoderFetch.Control.of_transfer fb).trans (fcontrol.trans (rcontrol.trans
        ((DecoderFetch.Control.of_clear fc).trans ((DecoderFetch.Control.of_transfer fd).trans
          (DecoderFetch.Control.of_transfer ft)))))))
  have unchanged (j : ℕ) (hj1 : j ≠ 1) (hj6 : j ≠ 6) (hj7 : j ≠ 7) (hj37 : j ≠ 37) :
      t.val.tapes j = s.val.tapes j := by
    rw [ht, hd, htC]
    simp only [Function.update_of_ne hj1, Function.update_of_ne hj6,
      Function.update_of_ne hj7, Function.update_of_ne hj37]
    change (RewindOvershoot.finish 1 xo f.val).tapes j = _
    simp only [RewindOvershoot.finish, Rewind.finishAt, Function.update_of_ne hj1]
    exact (ff.2.2.2.2.2.1 j hj1 hj6 hj7).trans
      (by
        rw [hb]
        simp only [Function.update_of_ne hj6]
        exact (fp.2.2.2.2.2.1 j hj1 hj1).trans (by simp [ha, hj1]))
  refine ⟨_, t, ?_, ea.seq (eP.seq (eb.seq (eF.seq (eR.seq (ec.seq (ed.seq et)))))) ,
    ⟨po, by simp [ht, fixedWidth_padWord]⟩, ?_,
    ⟨yo + (FixedWidth.bits clock.length (PadWord.bits xs)).length, by simp [ht]⟩,
    control, ?_⟩
  · simp only [FixedWidth.bits_length]
    omega
  · refine ⟨RationalAccumulator.blank_of_eq (unchanged 0 (by omega) (by omega) (by omega) (by omega)) hscratch.1,
      ⟨xo + (PadWord.bits xs).length, ?_⟩,
      RationalAccumulator.blank_of_eq (unchanged 2 (by omega) (by omega) (by omega) (by omega)) hscratch.2.2.1,
      RationalAccumulator.blank_of_eq (unchanged 3 (by omega) (by omega) (by omega) (by omega)) hscratch.2.2.2.1,
      RationalAccumulator.blank_of_eq (unchanged 5 (by omega) (by omega) (by omega) (by omega)) hscratch.2.2.2.2.1,
      ⟨wo + clock.length, ?_⟩,
      RationalAccumulator.blank_of_eq (unchanged 8 (by omega) (by omega) (by omega) (by omega)) hscratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (unchanged 9 (by omega) (by omega) (by omega) (by omega)) hscratch.2.2.2.2.2.2.2⟩
    · simp [ht, hd, htC]
    · simp [ht, hd]
  · exact ⟨control.1, control.2.1, control.2.2.1,
      fun j hj hj37 => unchanged j (by omega) (by omega) (by omega) hj37, control.2.2.2.2⟩


def writeCanonicalCode (widthBank indexBank baseBank clockBank source : ℕ) : Code :=
  .seq (packCanonicalCode source clockBank)
    (.seq (writeCode widthBank indexBank baseBank 37) (.call (TapeOps.clear 37)))

/-- A canonical natural word is padded, written to the actual indexed memory
slot, and all temporary tapes are reclaimed. Persistent operands are retained. -/
theorem write_canonical {n : ℕ} (widthBank indexBank baseBank clockBank source : ℕ)
    (hw : 10 ≤ widthBank) (hi : 10 ≤ indexBank) (hb : 10 ≤ baseBank)
    (hc : 10 ≤ clockBank) (hs : 10 ≤ source)
    (hw37 : widthBank ≠ 37) (hi37 : indexBank ≠ 37) (hb37 : baseBank ≠ 37)
    (input : List Bool) (tape : ℕ → Bool) (width index base clock : List Bool)
    (words : Vector (List Bool) n) (i : Fin n) (value : ℕ)
    (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hclock : clock.length = addressValue width) (hpositive : 0 < addressValue width)
    (hfit : value.bits.length ≤ addressValue width)
    (s : Store) (hscratch : Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (hwidthBank : Word s.val widthBank width) (hindexBank : Word s.val indexBank index)
    (hbaseBank : Word s.val baseBank base) (hclockBank : Word s.val clockBank clock)
    (hsource : RationalAccumulator.Word s.val source value)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) words) :
    ∃ cost t, cost ≤ costCap width index base (FixedWidth.bits (addressValue width) value.bits) +
        100 * addressValue width + 100 ∧
      Executes input tape (writeCanonicalCode widthBank indexBank baseBank clockBank source) cost s t ∧
      t.val.memory = MemoryWord.writeBits s.val.memory (addressValue base + i.val * addressValue width)
        (FixedWidth.bits (addressValue width) value.bits) ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width)
        (words.set i (FixedWidth.bits (addressValue width) value.bits)) ∧
      Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 37 ∧ FrameExcept 37 s.val t.val := by
  obtain ⟨pcost, p, hpcost, ep, hpword, hps, hp7, hpcontrol, hpf⟩ :=
    pack_canonical source clockBank hs hc input tape value.bits clock
      (by omega) (by omega) s hscratch h7 h37 hsource hclockBank
  have payload : Word p.val 37 (FixedWidth.bits (addressValue width) value.bits) := by
    simpa only [hclock] using hpword
  obtain ⟨wcost, w, hwcost, ew, hwmem, hwa, hws, hw7, hwf⟩ :=
    write_bank widthBank indexBank baseBank 37 hw hi hb (by omega) input tape
      width index base (FixedWidth.bits (addressValue width) value.bits) words i hwidth hindex
      (FixedWidth.bits_length _ _) p hps
      (word_of_eq (hpf.2.2.2.1 widthBank (Or.inr hw) hw37) hwidthBank)
      (word_of_eq (hpf.2.2.2.1 indexBank (Or.inr hi) hi37) hindexBank)
      (word_of_eq (hpf.2.2.2.1 baseBank (Or.inr hb) hb37) hbaseBank) payload
      (by simpa only [hpcontrol.2.2.2.1] using harray)
  obtain ⟨po, hpword⟩ := payload
  obtain ⟨t, et, ht, ft⟩ := WordCall.clear 37 input tape
    (FixedWidth.bits (addressValue width) value.bits) po w
    ((hwf.2.2.2.1 37 (by omega)).trans hpword)
  have unchanged (j : ℕ) (hj : j ≠ 37) : t.val.tapes j = w.val.tapes j := by simp [ht, hj]
  refine ⟨pcost + (wcost + (6 * (FixedWidth.bits (addressValue width) value.bits).length + 4)), t,
    ?_, ep.seq (ew.seq et), ?_, ?_, ?_, ?_,
    ⟨po + (FixedWidth.bits (addressValue width) value.bits).length, by simp [ht]⟩, ?_⟩
  · simp only [FixedWidth.bits_length]
    omega
  · exact ft.2.2.1.trans (hwmem.trans (congrArg
      (fun memory => MemoryWord.writeBits memory (addressValue base + i.val * addressValue width)
        (FixedWidth.bits (addressValue width) value.bits)) hpcontrol.2.2.2.1))
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
