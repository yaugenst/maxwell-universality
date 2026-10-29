import Maxwell.Cost.WordCall
import Maxwell.Cost.ArrayAccess

namespace Maxwell.Cost.DecoderFetch
open Structured

/-- Sequential channels, memory and caller registers retained by a fetch. -/
def Control (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧ t.memory = s.memory ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem Control.trans {s t u : BitRAMState} (h : Control s t) (k : Control t u) : Control s u := by
  rcases h with ⟨hi, hr, ho, hm, hg⟩
  rcases k with ⟨ki, kr, ko, km, kg⟩
  exact ⟨ki.trans hi, kr.trans hr, ko.trans ho, km.trans hm,
    fun i h15 h24 h25 h26 h27 h28 h29 =>
      (kg i h15 h24 h25 h26 h27 h28 h29).trans (hg i h15 h24 h25 h26 h27 h28 h29)⟩

theorem Control.of_transfer {a b : ℕ} {s t : BitRAMState}
    (h : WordTransfer.Frame a b s t) : Control s t := by
  rcases h with ⟨_, hi, hm, hr, ho, _, hg⟩
  exact ⟨hi, hr, ho, hm, fun i _ h24 h25 h26 h27 _ _ => hg i h24 h25 h26 h27⟩

theorem Control.of_clear {a : ℕ} {s t : BitRAMState}
    (h : TapeOps.Frame a a s t) : Control s t := by
  exact Control.of_transfer (WordTransfer.frame_of_copy h)

theorem Control.of_read {s t : BitRAMState} (h : ArrayAccess.Frame s t)
    (hm : t.memory = s.memory) : Control s t :=
  ⟨h.1, h.2.1, h.2.2.1, hm, h.2.2.2.2⟩

def prepare : Code := .seq (.call (WordTransfer.clone 64 1))
  (.seq (.call (WordTransfer.clone 45 5)) (.call (WordTransfer.clone 66 6)))

/-- Clone the fixed metadata bank into the arithmetic and address operands.
The bank's global tape states, including their head positions, are retained. -/
theorem prepare_executes (input : List Bool) (tape : ℕ → Bool)
    (width index clock : List Bool) (wo io co wbank ibank cbank : ℤ)
    (s : Store)
    (h1 : s.val.tapes 1 = {BitTape.blank with head := wo})
    (h5 : s.val.tapes 5 = {BitTape.blank with head := io})
    (h6 : s.val.tapes 6 = {BitTape.blank with head := co})
    (h64 : s.val.tapes 64 = BitTape.shifted width wbank)
    (h45 : s.val.tapes 45 = BitTape.shifted index ibank)
    (h66 : s.val.tapes 66 = BitTape.shifted clock cbank) :
    ∃ t, Executes input tape prepare (15 * (width.length + index.length + clock.length) + 51) s t ∧
      t.val.tapes = Function.update (Function.update (Function.update s.val.tapes
        1 (BitTape.shifted width wo)) 5 (BitTape.shifted index io)) 6 (BitTape.shifted clock co) ∧
      Control s.val t.val := by
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clone 64 1 (by decide) input tape width wbank wo s h64 h1
  obtain ⟨b, eb, hb, fb⟩ := WordCall.clone 45 5 (by decide) input tape index ibank io a
    (by simpa [ha] using h45) (by simpa [ha] using h5)
  obtain ⟨t, et, ht, ft⟩ := WordCall.clone 66 6 (by decide) input tape clock cbank co b
    (by simpa [hb, ha] using h66) (by simpa [hb, ha] using h6)
  refine ⟨t, ?_, by rw [ht, hb, ha],
    (Control.of_transfer fa).trans ((Control.of_transfer fb).trans (Control.of_transfer ft))⟩
  convert ea.seq (eb.seq et) using 1 <;> first | rfl | omega

end Maxwell.Cost.DecoderFetch
