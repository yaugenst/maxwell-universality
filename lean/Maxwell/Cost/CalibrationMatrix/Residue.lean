import Maxwell.Cost.CalibrationMatrix.EntryPrepared
import Maxwell.Cost.BankArray.Common
import Maxwell.Cost.NormalizeWord

/-! Actual modulus-20 extraction with reusable arithmetic scratch. -/
namespace Maxwell.Cost.CalibrationMatrix.Residue
open Structured RationalAccumulator
set_option maxHeartbeats 1000000

def changes (target : ℕ) : Finset ℕ := {0, 1, 2, 3, 4, target}

def code (radixBank source target : ℕ) : Code :=
  .seq (Entry.prepareCode radixBank source)
    (.seq (Entry.digitCode target)
      (.seq (WordCall.eraseEnd 3)
        (.seq (.call (TapeOps.clear 1)) (.call (NormalizeWord.program target)))))

/-- The constant divisor is read from its persistent bank; the dividend is
copied from the actual coordinate word. The returned remainder is canonical. -/
theorem executes (radixBank source target : ℕ) (hrb : 100 ≤ radixBank)
    (hsource : 100 ≤ source) (htarget : 10 ≤ target)
    (input : List Bool) (tape : ℕ → Bool) (word : List Bool) (s : Store)
    (hr : BankArray.Word s.val radixBank (20 : ℕ).bits)
    (hw : BankArray.Word s.val source word) (ht : Blank s.val target)
    (hb : ∀ i, i < 5 → Blank s.val i) :
    ∃ cost t, cost ≤ 700 * (word.length + 8) ^ 2 ∧
      Executes input tape (code radixBank source target) cost s t ∧
      Word t.val target (addressValue word % 20) ∧
      (addressValue word % 20).size ≤ 5 ∧
      (∀ i, i < 5 → Blank t.val i) ∧
      BinaryPrecision.Frame (changes target) s.val t.val := by
  obtain ⟨ro, hr⟩ := hr
  obtain ⟨wo, hw⟩ := hw
  obtain ⟨a, ea, ha, fa⟩ := Entry.prepare radixBank source (by omega) (by omega)
    input tape (20 : ℕ).bits word ro wo s hr hw hb
  have hat : Blank a.val target := blank_of_eq (fa.tapes target (by simp; omega)) ht
  obtain ⟨dc, b, remainder, quotient, hdc, eb, hp, hrem, hv, _, hrl, hql, fb⟩ :=
    Entry.digit target (by omega) input tape (20 : ℕ).bits word (by rw [addressValue_bits]; decide) a ha hat
  obtain ⟨h0, ⟨ro', hr'⟩, h2, ⟨qo, hq⟩, h4⟩ := hp
  obtain ⟨mo, hm⟩ := hrem
  obtain ⟨c, ec, ctapes, fc⟩ := WordCall.erase_end 3 input tape quotient qo b hq
  have hc1 : c.val.tapes 1 = BitTape.shifted (20 : ℕ).bits ro' := by simp [ctapes, hr']
  obtain ⟨d, ed, dtapes, fd⟩ := WordCall.clear 1 input tape (20 : ℕ).bits ro' c hc1
  have hdm : d.val.tapes target = BitTape.shifted remainder mo := by
    simpa [dtapes, ctapes, show target ≠ 1 by omega, show target ≠ 3 by omega] using hm
  obtain ⟨nc, result, hnc, en, hnp, hn, _, fn⟩ :=
    NormalizeWord.simulation target mo input tape remainder d.val d.property hdm
  let t := Store.ofState result
  have et : Executes input tape (.call (NormalizeWord.program target)) (nc + 1) d t :=
    .call _ d result _ en (by simp [NormalizeWord.program, hnp, ScanForward.program, TapeOps.trim,
      Rewind.program, BitRAMInstruction.relocate])
  have normFrame : BinaryPrecision.Frame (changes target) d.val t.val := by
    refine ⟨fn.1, fn.2.1, fn.2.2.1, fn.2.2.2.1, fn.2.2.2.2.1, ?_⟩
    intro i hi
    apply fn.2.2.2.2.2.1 i
    simp only [changes, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    tauto
  have prepFrame : BinaryPrecision.Frame (changes target) s.val a.val := fa.mono (by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [changes])
  have digitFrame : BinaryPrecision.Frame (changes target) a.val b.val := by
    refine ⟨fb.1, fb.2.1, fb.2.2.1, fb.2.2.2.1, fb.2.2.2.2.1, ?_⟩
    intro i hi
    simp only [changes, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact fb.2.2.2.2.2.1 i (by omega) (by tauto)
  have clearFrame : BinaryPrecision.Frame (changes target) b.val d.val := by
    refine ⟨fd.1.trans fc.1, fd.2.1.trans fc.2.1, fd.2.2.1.trans fc.2.2.1,
      fd.2.2.2.1.trans fc.2.2.2.1, fd.2.2.2.2.1.trans fc.2.2.2.2.1, ?_⟩
    intro i hi
    have h : i ≠ 1 ∧ i ≠ 3 := by
      simp only [changes, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      tauto
    simp [dtapes, ctapes, h.1, h.2]
  have keep (i : ℕ) (hi : i ≠ target) : t.val.tapes i = d.val.tapes i := fn.2.2.2.2.2.1 i hi
  have h20 : (20 : ℕ).bits.length = 5 := by decide
  rw [h20] at hdc hrl
  rw [addressValue_bits] at hv
  refine ⟨15 * (20 : ℕ).bits.length + 20 * word.length + 38 +
      (dc + (10 * quotient.length + 10 + (6 * (20 : ℕ).bits.length + 4 + (nc + 1)))),
    t, ?_, ea.seq (eb.seq (ec.seq (ed.seq et))), ?_, ?_, ?_,
    ((prepFrame.trans digitFrame).trans clearFrame).trans normFrame⟩
  · rw [h20, hql]
    nlinarith
  · exact ⟨mo, by simpa only [t, Store.ofState, hv] using hn⟩
  · apply Nat.size_le.mpr
    have h := Nat.mod_lt (addressValue word) (by decide : 0 < 20)
    norm_num
    omega
  · intro i hi
    interval_cases i
    · exact blank_of_eq ((keep 0 (by omega)).trans (by simp [dtapes, ctapes])) h0
    · exact ⟨ro' + (20 : ℕ).bits.length, (keep 1 (by omega)).trans (by simp [dtapes])⟩
    · exact blank_of_eq ((keep 2 (by omega)).trans (by simp [dtapes, ctapes])) h2
    · exact ⟨qo + quotient.length, (keep 3 (by omega)).trans (by simp [dtapes, ctapes])⟩
    · exact blank_of_eq ((keep 4 (by omega)).trans (by simp [dtapes, ctapes])) h4

end Maxwell.Cost.CalibrationMatrix.Residue
