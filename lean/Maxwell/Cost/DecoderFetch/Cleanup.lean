import Maxwell.Cost.DecoderFetch.Prepare
import Maxwell.Cost.WordReset

namespace Maxwell.Cost.DecoderFetch
open Structured

def cleanup : Code := .seq (.call (TapeOps.clear 1))
  (.seq (WordCall.eraseEnd 5) (.seq (WordCall.eraseEnd 6) (WordCall.resetStart 45)))

/-- Reclaim the computed address, cloned metadata and consumed term index.
The fetched sample remains intact on tape 7. -/
theorem cleanup_executes (input : List Bool) (tape : ℕ → Bool)
    (width address clock index : List Bool) (wo ao co io : ℤ) (s : Store)
    (h1 : s.val.tapes 1 = BitTape.shifted width wo)
    (h5 : s.val.tapes 5 = BitTape.shiftedEnd address ao)
    (h6 : s.val.tapes 6 = BitTape.shiftedEnd clock co)
    (h45 : s.val.tapes 45 = BitTape.shifted index io) :
    ∃ t, Executes input tape cleanup
        (6 * width.length + 10 * address.length + 10 * clock.length + 11 * index.length + 34) s t ∧
      t.val.tapes = Function.update (Function.update (Function.update (Function.update s.val.tapes
        1 {BitTape.blank with head := wo + width.length})
        5 {BitTape.blank with head := ao + address.length})
        6 {BitTape.blank with head := co + clock.length})
        45 {BitTape.blank with head := io} ∧ Control s.val t.val := by
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clear 1 input tape width wo s h1
  obtain ⟨b, eb, hb, fb⟩ := WordCall.erase_end 5 input tape address ao a (by simpa [ha] using h5)
  obtain ⟨c, ec, hc, fc⟩ := WordCall.erase_end 6 input tape clock co b (by simpa [hb, ha] using h6)
  obtain ⟨t, et, ht, ft⟩ := WordCall.reset_start 45 input tape index io c (by simpa [hc, hb, ha] using h45)
  refine ⟨t, ?_, by rw [ht, hc, hb, ha],
    (Control.of_clear fa).trans ((Control.of_transfer fb).trans
      ((Control.of_transfer fc).trans (Control.of_transfer ft)))⟩
  convert ea.seq (eb.seq (ec.seq et)) using 1 <;> first | rfl | omega

end Maxwell.Cost.DecoderFetch
