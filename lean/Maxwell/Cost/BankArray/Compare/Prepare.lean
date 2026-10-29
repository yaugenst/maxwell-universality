import Maxwell.Cost.BankArray.Common
import Maxwell.Cost.Subtraction

namespace Maxwell.Cost.BankArray
open Structured
open RationalAccumulator (Blank)

def comparePrepare (left right : ℕ) : Code := .seq (.call (WordTransfer.clone left 0))
  (.seq (.call (WordTransfer.clone right 1)) (.call Subtraction.program))

/-- Exact comparison on saved equal-width words, with the subtraction output
left as a concrete tape word for the following cleanup. -/
theorem compare_prepare (left right : ℕ) (hl : 10 ≤ left) (hr : 10 ≤ right)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : List Bool) (hlen : xs.length = ys.length)
    (xo yo zo : ℤ) (s : Store) (hxs : Word s.val left xs) (hys : Word s.val right ys)
    (h0 : s.val.tapes 0 = {BitTape.blank with head := xo})
    (h1 : s.val.tapes 1 = {BitTape.blank with head := yo})
    (h2 : s.val.tapes 2 = {BitTape.blank with head := zo}) :
    ∃ t, Executes input tape (comparePrepare left right) (50 * xs.length + 44) s t ∧
      (t.val.registers 2 = true ↔ addressValue xs < addressValue ys) ∧
      t.val.tapes 0 = BitTape.shiftedEnd xs xo ∧
      t.val.tapes 1 = BitTape.shiftedEnd ys yo ∧
      t.val.tapes 2 = BitTape.shiftedEnd (Subtraction.result false xs ys).1 zo ∧
      Control s.val t.val ∧ (∀ i, 3 ≤ i → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨lo, hxs⟩ := hxs
  obtain ⟨ro, hys⟩ := hys
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clone left 0 (by omega) input tape xs lo xo s hxs h0
  obtain ⟨b, eb, hb, fb⟩ := WordCall.clone right 1 (by omega) input tape ys ro yo a
    (by simpa [ha, show right ≠ 0 by omega] using hys) (by simpa [ha] using h1)
  have hb0 : b.val.tapes 0 = BitTape.shifted xs xo := by simp [hb, ha]
  have hb1 : b.val.tapes 1 = BitTape.shifted ys yo := by simp [hb]
  obtain ⟨t, et, hp, ht2, hwrite, ht0, ht1, hf⟩ := Subtraction.simulation input tape b.val xs ys b.property
    (hb0 ▸ BitTape.shifted_represents xs xo) (hb1 ▸ BitTape.shifted_represents ys yo)
  have es : Executes input tape (.call Subtraction.program) (20 * max xs.length ys.length + 10)
      b (Store.ofState t) := .call _ b t _ et (by rw [hp]; rfl)
  have hmax : max xs.length ys.length = xs.length := by omega
  have hframe := hf
  simp only [rippleFrame, Prod.mk.injEq] at hframe
  rcases hframe with ⟨_, hinput, hmem, hrandom, houtput, hregs, htapes⟩
  have subControl : Control b.val t := by
    refine ⟨hinput, hrandom, houtput, hmem, ?_⟩
    intro i hi _ _ _ _ _ _
    simpa [Nat.sub_add_cancel (show 12 ≤ i by omega)] using congrFun hregs (i - 12)
  refine ⟨Store.ofState t, ?_, ?_, ?_, ?_, hwrite.blank (by simpa [hb, ha] using h2),
    (DecoderFetch.Control.of_transfer fa).trans ((DecoderFetch.Control.of_transfer fb).trans subControl), ?_⟩
  · convert ea.seq (eb.seq es) using 1 <;> first | rfl | omega
  · rw [show (Store.ofState t).val.registers 2 = t.registers 2 from rfl, ht2]
    exact Subtraction.final_borrow_iff xs ys
  · simpa [Store.ofState, hb0, BitTape.shiftedEnd, BitTape.shifted, hmax] using ht0
  · simpa [Store.ofState, hb1, BitTape.shiftedEnd, BitTape.shifted, hmax, hlen] using ht1
  · intro i hi
    have he := congrFun htapes (i - 3)
    simp only [Nat.sub_add_cancel hi] at he
    simpa [Store.ofState, hb, ha, show i ≠ 0 by omega, show i ≠ 1 by omega] using he

end Maxwell.Cost.BankArray
