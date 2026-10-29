import Maxwell.Cost.DecoderFetch.Prepare

namespace Maxwell.Cost.BankArray
open Structured
abbrev Control := DecoderFetch.Control

/-- Four persistent bank words supply width, index, base address and payload.
All parameters are fixed tape identifiers in the finite code. -/
def prepare (widthBank indexBank baseBank payloadBank : ℕ) : Code :=
  .seq (.call (WordTransfer.clone widthBank 1))
  (.seq (.call (WordTransfer.clone indexBank 5))
  (.seq (.call (WordTransfer.clone baseBank 8)) (.call (WordTransfer.clone payloadBank 6))))

theorem prepare_executes (widthBank indexBank baseBank payloadBank : ℕ)
    (hw : 10 ≤ widthBank) (hi : 10 ≤ indexBank) (hb : 10 ≤ baseBank) (hp : 10 ≤ payloadBank)
    (input : List Bool) (tape : ℕ → Bool) (width index base payload : List Bool)
    (wo io bo po wbank ibank bbank pbank : ℤ) (s : Store)
    (h1 : s.val.tapes 1 = {BitTape.blank with head := wo})
    (h5 : s.val.tapes 5 = {BitTape.blank with head := io})
    (h8 : s.val.tapes 8 = {BitTape.blank with head := bo})
    (h6 : s.val.tapes 6 = {BitTape.blank with head := po})
    (hwidth : s.val.tapes widthBank = BitTape.shifted width wbank)
    (hindex : s.val.tapes indexBank = BitTape.shifted index ibank)
    (hbase : s.val.tapes baseBank = BitTape.shifted base bbank)
    (hpayload : s.val.tapes payloadBank = BitTape.shifted payload pbank) :
    ∃ t, Executes input tape (prepare widthBank indexBank baseBank payloadBank)
        (15 * (width.length + index.length + base.length + payload.length) + 68) s t ∧
      t.val.tapes = Function.update (Function.update (Function.update (Function.update s.val.tapes
        1 (BitTape.shifted width wo)) 5 (BitTape.shifted index io))
        8 (BitTape.shifted base bo)) 6 (BitTape.shifted payload po) ∧ Control s.val t.val := by
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clone widthBank 1 (by omega) input tape width wbank wo s hwidth h1
  obtain ⟨b, eb, ht, fb⟩ := WordCall.clone indexBank 5 (by omega) input tape index ibank io a
    (by simpa [ha, show indexBank ≠ 1 by omega] using hindex) (by simpa [ha] using h5)
  obtain ⟨c, ec, hc, fc⟩ := WordCall.clone baseBank 8 (by omega) input tape base bbank bo b
    (by simpa [ht, ha, show baseBank ≠ 1 by omega, show baseBank ≠ 5 by omega] using hbase)
    (by simpa [ht, ha] using h8)
  obtain ⟨t, et, he, fe⟩ := WordCall.clone payloadBank 6 (by omega) input tape payload pbank po c
    (by simpa [hc, ht, ha, show payloadBank ≠ 1 by omega,
      show payloadBank ≠ 5 by omega, show payloadBank ≠ 8 by omega] using hpayload)
    (by simpa [hc, ht, ha] using h6)
  refine ⟨t, ?_, by rw [he, hc, ht, ha],
    (DecoderFetch.Control.of_transfer fa).trans ((DecoderFetch.Control.of_transfer fb).trans
      ((DecoderFetch.Control.of_transfer fc).trans (DecoderFetch.Control.of_transfer fe)))⟩
  convert ea.seq (eb.seq (ec.seq et)) using 1 <;> first | rfl | omega

def cleanup : Code := .seq (.call (TapeOps.clear 1))
  (.seq (WordCall.eraseEnd 5) (.seq (WordCall.eraseEnd 6) (.call (TapeOps.clear 8))))

theorem cleanup_executes (input : List Bool) (tape : ℕ → Bool)
    (width address payload base : List Bool) (wo ao po bo : ℤ) (s : Store)
    (h1 : s.val.tapes 1 = BitTape.shifted width wo)
    (h5 : s.val.tapes 5 = BitTape.shiftedEnd address ao)
    (h6 : s.val.tapes 6 = BitTape.shiftedEnd payload po)
    (h8 : s.val.tapes 8 = BitTape.shifted base bo) :
    ∃ t, Executes input tape cleanup
        (6 * width.length + 10 * address.length + 10 * payload.length + 6 * base.length + 28) s t ∧
      t.val.tapes = Function.update (Function.update (Function.update (Function.update s.val.tapes
        1 {BitTape.blank with head := wo + width.length})
        5 {BitTape.blank with head := ao + address.length})
        6 {BitTape.blank with head := po + payload.length})
        8 {BitTape.blank with head := bo + base.length} ∧ Control s.val t.val := by
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clear 1 input tape width wo s h1
  obtain ⟨b, eb, hb, fb⟩ := WordCall.erase_end 5 input tape address ao a (by simpa [ha] using h5)
  obtain ⟨c, ec, hc, fc⟩ := WordCall.erase_end 6 input tape payload po b (by simpa [hb, ha] using h6)
  obtain ⟨t, et, ht, ft⟩ := WordCall.clear 8 input tape base bo c (by simpa [hc, hb, ha] using h8)
  refine ⟨t, ?_, by rw [ht, hc, hb, ha],
    (DecoderFetch.Control.of_clear fa).trans ((DecoderFetch.Control.of_transfer fb).trans
      ((DecoderFetch.Control.of_transfer fc).trans (DecoderFetch.Control.of_clear ft)))⟩
  convert ea.seq (eb.seq (ec.seq et)) using 1 <;> first | rfl | omega

end Maxwell.Cost.BankArray
