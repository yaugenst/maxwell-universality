import Maxwell.Cost.BankArray.Compare.Prepare

namespace Maxwell.Cost.BankArray
open Structured
open RationalAccumulator (Blank)

def compareCleanup : Code := .seq (WordCall.eraseEnd 0)
  (.seq (WordCall.eraseEnd 1) (WordCall.eraseEnd 2))

def compareCode (left right : ℕ) : Code := .seq (comparePrepare left right) compareCleanup

/-- Uniform unsigned comparison of stored equal-width words. Every temporary
word is reclaimed and the result is the actual Boolean borrow register. -/
theorem compare_bank (left right : ℕ) (hl : 10 ≤ left) (hr : 10 ≤ right)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : List Bool) (hlen : xs.length = ys.length)
    (s : Store) (hxs : Word s.val left xs) (hys : Word s.val right ys) (hs : Scratch s.val) :
    ∃ t, Executes input tape (compareCode left right) (80 * xs.length + 74) s t ∧
      (t.val.registers 2 = true ↔ addressValue xs < addressValue ys) ∧
      Scratch t.val ∧ t.val.memory = s.val.memory ∧
      (∀ i, 3 ≤ i → t.val.tapes i = s.val.tapes i) ∧ Frame s.val t.val := by
  rcases hs with ⟨⟨xo, h0⟩, ⟨yo, h1⟩, ⟨zo, h2⟩, h3, h5, h6, h8, h9⟩
  obtain ⟨p, ep, hp2, hp0, hp1, hpout, pf, pt⟩ :=
    compare_prepare left right hl hr input tape xs ys hlen xo yo zo s hxs hys h0 h1 h2
  obtain ⟨a, ea, ha, fa⟩ := WordCall.erase_end 0 input tape xs xo p hp0
  obtain ⟨b, eb, hb, fb⟩ := WordCall.erase_end 1 input tape ys yo a (by simpa [ha] using hp1)
  obtain ⟨t, et, ht, ft⟩ := WordCall.erase_end 2 input tape (Subtraction.result false xs ys).1 zo b
    (by simpa [hb, ha] using hpout)
  have hresult : (Subtraction.result false xs ys).1.length = xs.length := by
    rw [Subtraction.result_length]
    omega
  have hglobal : t.val.tapes = Function.update (Function.update (Function.update p.val.tapes
      0 {BitTape.blank with head := xo + xs.length})
      1 {BitTape.blank with head := yo + ys.length})
      2 {BitTape.blank with head := zo + (Subtraction.result false xs ys).1.length} := by rw [ht, hb, ha]
  have keep (i : ℕ) (hi : 3 ≤ i) : t.val.tapes i = s.val.tapes i := by
    rw [hglobal]
    simp only [Function.update_apply, show i ≠ 0 by omega, show i ≠ 1 by omega,
      show i ≠ 2 by omega, ↓reduceIte]
    exact pt i hi
  have control := pf.trans ((DecoderFetch.Control.of_transfer fa).trans
    ((DecoderFetch.Control.of_transfer fb).trans (DecoderFetch.Control.of_transfer ft)))
  have boolkeep : t.val.registers 2 = p.val.registers 2 :=
    (ft.2.2.2.2.2.2 2 (by omega) (by omega) (by omega) (by omega)).trans
      ((fb.2.2.2.2.2.2 2 (by omega) (by omega) (by omega) (by omega)).trans
        (fa.2.2.2.2.2.2 2 (by omega) (by omega) (by omega) (by omega)))
  refine ⟨t, ?_, by simpa [boolkeep] using hp2, ?_, control.2.2.2.1, keep,
    ⟨control.1, control.2.1, control.2.2.1, fun i hi => keep i (by omega), control.2.2.2.2⟩⟩
  · convert ep.seq (ea.seq (eb.seq et)) using 1 <;> first | rfl | omega
  · exact ⟨⟨xo + xs.length, by simp [hglobal]⟩,
      ⟨yo + ys.length, by simp [hglobal]⟩,
      ⟨zo + (Subtraction.result false xs ys).1.length, by simp [hglobal]⟩,
      RationalAccumulator.blank_of_eq (keep 3 (by omega)) h3,
      RationalAccumulator.blank_of_eq (keep 5 (by omega)) h5,
      RationalAccumulator.blank_of_eq (keep 6 (by omega)) h6,
      RationalAccumulator.blank_of_eq (keep 8 (by omega)) h8,
      RationalAccumulator.blank_of_eq (keep 9 (by omega)) h9⟩

end Maxwell.Cost.BankArray
