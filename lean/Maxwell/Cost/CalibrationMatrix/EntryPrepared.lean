import Maxwell.Cost.CalibrationMatrix.Entry
import Maxwell.Cost.BinaryPrecision

/-! Actual loading of mixed-radix inputs from persistent word banks. -/
namespace Maxwell.Cost.CalibrationMatrix.Entry
open Structured RationalAccumulator
set_option maxHeartbeats 800000

def prepareCode (radixBank indexBank : ℕ) : Code :=
  .seq (.call (WordTransfer.clone radixBank 1))
    (.seq (.call (WordTransfer.clone indexBank 3)) (.call (ScanForward.program 3)))

theorem prepare (radixBank indexBank : ℕ) (hradix : 5 ≤ radixBank) (hindex : 5 ≤ indexBank)
    (input : List Bool) (randomTape : ℕ → Bool) (radix index : List Bool)
    (ro io : ℤ) (s : Store)
    (hr : s.val.tapes radixBank = BitTape.shifted radix ro)
    (hi : s.val.tapes indexBank = BitTape.shifted index io)
    (hblank : ∀ k, k < 5 → Blank s.val k) :
    ∃ t, Executes input randomTape (prepareCode radixBank indexBank)
        (15 * radix.length + 20 * index.length + 38) s t ∧
      Prepared t.val radix index ∧ BinaryPrecision.Frame {1, 3} s.val t.val := by
  obtain ⟨o1, h1⟩ := hblank 1 (by decide)
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clone radixBank 1 (by omega)
    input randomTape radix ro o1 s hr h1
  obtain ⟨o3, h3⟩ := hblank 3 (by decide)
  have ha3 : a.val.tapes 3 = {BitTape.blank with head := o3} := by simpa [ha] using h3
  have hai : a.val.tapes indexBank = BitTape.shifted index io := by
    simpa [ha, show indexBank ≠ 1 by omega] using hi
  obtain ⟨b, eb, hb, fb⟩ := WordCall.clone indexBank 3 (by omega)
    input randomTape index io o3 a hai ha3
  have hb3 : b.val.tapes 3 = BitTape.shifted index o3 := by simp [hb]
  have escan := ScanForward.shifted_steps 3 o3 input randomTape index b.val b.property hb3
  let t := Store.ofState (ScanForward.finish 3 index.length b.val)
  have et : Executes input randomTape (.call (ScanForward.program 3)) (5 * index.length + 4) b t :=
    .call _ b _ _ escan.1 (by simp [ScanForward.program, ScanForward.finish])
  have tapes (k : ℕ) (hk1 : k ≠ 1) (hk3 : k ≠ 3) : t.val.tapes k = s.val.tapes k := by
    have hscan := escan.2.2.2.2.2.2.2.1 k hk3 hk3
    exact hscan.trans (by simp [hb, ha, hk1, hk3])
  have ht1 : t.val.tapes 1 = BitTape.shifted radix o1 :=
    (escan.2.2.2.2.2.2.2.1 1 (by decide) (by decide)).trans (by simp [hb, ha])
  refine ⟨t, ?_, ?_, ?_⟩
  · convert ea.seq (eb.seq et) using 1 <;> first | rfl | omega
  · exact ⟨RationalAccumulator.blank_of_eq (tapes 0 (by decide) (by decide)) (hblank 0 (by decide)),
      ⟨o1, ht1⟩,
      RationalAccumulator.blank_of_eq (tapes 2 (by decide) (by decide)) (hblank 2 (by decide)),
      ⟨o3, escan.2.1⟩,
      RationalAccumulator.blank_of_eq (tapes 4 (by decide) (by decide)) (hblank 4 (by decide))⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact escan.2.2.1.trans (fb.1.trans fa.1)
    · exact escan.2.2.2.1.trans (fb.2.1.trans fa.2.1)
    · exact escan.2.2.2.2.1.trans (fb.2.2.1.trans fa.2.2.1)
    · exact escan.2.2.2.2.2.1.trans (fb.2.2.2.1.trans fa.2.2.2.1)
    · exact escan.2.2.2.2.2.2.1.trans (fb.2.2.2.2.1.trans fa.2.2.2.2.1)
    · intro k hk
      have h : k ≠ 1 ∧ k ≠ 3 := by simpa using hk
      exact tapes k h.1 h.2

end Maxwell.Cost.CalibrationMatrix.Entry
