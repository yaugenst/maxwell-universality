import Maxwell.Cost.CalibrationMatrix.Correctness
import Maxwell.Cost.WordSwap

namespace Maxwell.Cost.CalibrationMatrix
open Structured
open RationalAccumulator (Blank)

/-- The read/write buffer descriptors are physically swapped after use. -/
def recycleCode : Code := .seq (.call (TapeOps.clear 102))
  (.seq (.call (TapeOps.clear 104))
    (.seq (WordSwap.code 112 114 109) (WordSwap.code 113 115 109)))

def RecycleFrame (s t : BitRAMState) : Prop :=
  t.memory = s.memory ∧ t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ 102 → i ≠ 104 → i ≠ 109 → i ≠ 112 → i ≠ 113 → i ≠ 114 → i ≠ 115 →
    t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem recycle (input : List Bool) (tape : ℕ → Bool)
    (mi ri vp vn op on : List Bool) (s : Store)
    (hmi : BankArray.Word s.val 102 mi) (hri : BankArray.Word s.val 104 ri)
    (hvp : BankArray.Word s.val 112 vp) (hvn : BankArray.Word s.val 113 vn)
    (hop : BankArray.Word s.val 114 op) (hon : BankArray.Word s.val 115 on)
    (h109 : Blank s.val 109) :
    ∃ t, Executes input tape recycleCode
        (6*mi.length+4+(6*ri.length+4+
          (12*(2*vp.length+op.length)+33+(12*(2*vn.length+on.length)+33)))) s t ∧
      BankArray.Word t.val 102 [] ∧ BankArray.Word t.val 104 [] ∧
      BankArray.Word t.val 112 op ∧ BankArray.Word t.val 113 on ∧
      BankArray.Word t.val 114 vp ∧ BankArray.Word t.val 115 vn ∧ Blank t.val 109 ∧ RecycleFrame s.val t.val := by
  obtain ⟨mo, hmi⟩ := hmi
  obtain ⟨ro, hri⟩ := hri
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clear 102 input tape mi mo s hmi
  obtain ⟨b, eb, hb, fb⟩ := WordCall.clear 104 input tape ri ro a (by simpa [ha] using hri)
  have keepB (i : ℕ) (h102 : i ≠ 102) (h104 : i ≠ 104) : b.val.tapes i = s.val.tapes i := by
    simp [hb, ha, h102, h104]
  obtain ⟨c, ec, hc112, hc114, hc109, fc⟩ := WordSwap.executes 112 114 109 (by omega) (by omega) (by omega)
    input tape vp op b (BankArray.word_of_eq (keepB 112 (by omega) (by omega)) hvp)
      (BankArray.word_of_eq (keepB 114 (by omega) (by omega)) hop)
      (RationalAccumulator.blank_of_eq (keepB 109 (by omega) (by omega)) h109)
  have keepC (i : ℕ) (h112 : i ≠ 112) (h114 : i ≠ 114) (h109 : i ≠ 109) : c.val.tapes i = b.val.tapes i :=
    fc.2.2.2.2.2.1 i h112 h114 h109
  obtain ⟨t, et, ht113, ht115, ht109, ft⟩ := WordSwap.executes 113 115 109 (by omega) (by omega) (by omega)
    input tape vn on c
      (BankArray.word_of_eq ((keepC 113 (by omega) (by omega) (by omega)).trans (keepB 113 (by omega) (by omega))) hvn)
      (BankArray.word_of_eq ((keepC 115 (by omega) (by omega) (by omega)).trans (keepB 115 (by omega) (by omega))) hon) hc109
  have keepT (i : ℕ) (h113 : i ≠ 113) (h115 : i ≠ 115) (h109 : i ≠ 109) : t.val.tapes i = c.val.tapes i :=
    ft.2.2.2.2.2.1 i h113 h115 h109
  refine ⟨t, ea.seq (eb.seq (ec.seq et)), ?_, ?_,
    BankArray.word_of_eq (keepT 112 (by omega) (by omega) (by omega)) hc112, ht113,
    BankArray.word_of_eq (keepT 114 (by omega) (by omega) (by omega)) hc114, ht115, ht109, ?_⟩
  · refine ⟨mo+mi.length, ?_⟩
    rw [keepT 102 (by omega) (by omega) (by omega), keepC 102 (by omega) (by omega) (by omega)]
    simp [hb, ha, BitTape.shifted, BitTape.blank]
  · refine ⟨ro+ri.length, ?_⟩
    rw [keepT 104 (by omega) (by omega) (by omega), keepC 104 (by omega) (by omega) (by omega)]
    simp [hb, BitTape.shifted, BitTape.blank]
  · exact ⟨ft.2.2.1.trans (fc.2.2.1.trans (fb.2.2.1.trans fa.2.2.1)),
      ft.2.1.trans (fc.2.1.trans (fb.2.1.trans fa.2.1)),
      ft.2.2.2.1.trans (fc.2.2.2.1.trans (fb.2.2.2.1.trans fa.2.2.2.1)),
      ft.2.2.2.2.1.trans (fc.2.2.2.2.1.trans (fb.2.2.2.2.1.trans fa.2.2.2.2.1)),
      fun i h102 h104 h109 h112 h113 h114 h115 =>
        (keepT i h113 h115 h109).trans ((keepC i h112 h114 h109).trans (keepB i h102 h104)),
      fun i h24 h25 h26 h27 => (ft.2.2.2.2.2.2 i h24 h25 h26 h27).trans
        ((fc.2.2.2.2.2.2 i h24 h25 h26 h27).trans
          ((fb.2.2.2.2.2.2 i h26 h27).trans (fa.2.2.2.2.2.2 i h26 h27)))⟩

end Maxwell.Cost.CalibrationMatrix
