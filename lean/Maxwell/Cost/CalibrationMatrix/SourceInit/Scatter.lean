import Maxwell.Cost.CalibrationMatrix.SourceInit.Target
import Maxwell.Cost.CalibrationMatrix.SourceInit.Fill

namespace Maxwell.Cost.CalibrationMatrix.SourceInit

open Structured
open RationalAccumulator (Blank)
open scoped BigOperators

set_option maxHeartbeats 800000

def scatterCode : Code := .seq targetCode
  (.seq (addPairCode 104 120 121) (.seq (addPairCode 102 161 162) writeCode))

/-- One physical sparse record is accumulated into all four dense arrays. -/
theorem scatter {m n : ℕ} (d : Data m n) (B : ℕ) (hd : d.Sized B)
    (hp : (∑ j, d.records.positive j).bits.length ≤ addressValue d.width)
    (hn : (∑ j, d.records.negative j).bits.length ≤ addressValue d.width)
    (j : Fin m) (input : List Bool) (tape : ℕ → Bool) (index old : List Bool)
    (hindex : addressValue index = j.val) (hilen : index.length ≤ B) (holen : old.length ≤ B)
    (s : Store) (hready : Ready s.val (dotValues 0 0))
    (hdata : Stored d (outputWords d j.val) s.val)
    (h102 : BankArray.Word s.val 102 index) (h104 : BankArray.Word s.val 104 old) (h37 : Blank s.val 37) :
    ∃ cost t, cost ≤ 291000*(B+2)^2 ∧ Executes input tape scatterCode cost s t ∧
      Ready t.val (dotValues 0 0) ∧ Stored d (outputWords d (j.val+1)) t.val ∧
      BankArray.Word t.val 104 (d.records.index j).val.bits ∧
      (d.records.index j).val.bits.length ≤ B ∧ Blank t.val 37 ∧
      MatrixFrame s.val t.val ∧ Outside d s.val t.val ∧
      (∀ i, i = 102 ∨ i = 103 ∨ i = 106 ∨ i = 108 → t.val.tapes i = s.val.tapes i) := by
  let row := d.records.index j
  let p := (values d.records j.val).positive row
  let q := (values d.records j.val).negative row
  have hpfit := values_positive_bits_le d.records j.val _ hp row
  have hnfit := values_negative_bits_le d.records j.val _ hn row
  have hnextp : (p+d.records.positive j).bits.length ≤ addressValue d.width := by
    simpa only [values_step_positive, row, Function.update_self] using
      values_positive_bits_le d.records (j.val+1) _ hp row
  have hnextn : (q+d.records.negative j).bits.length ≤ addressValue d.width := by
    simpa only [values_step_negative, row, Function.update_self] using
      values_negative_bits_le d.records (j.val+1) _ hn row
  obtain ⟨c0, a, hc0, e0, r0, data0, i0, hi0, hm0, f0⟩ :=
    load_target d (outputWords d j.val) B hd j input tape index old hindex hilen holen
      s (dotValues 0 0) hready hdata h102 h104
  have index0 := BankArray.word_of_eq (f0.2.2.2.1 102 (by omega) (by omega)) h102
  have blank0 := RationalAccumulator.blank_of_eq (f0.2.2.2.1 37 (by omega) (by omega)) h37
  obtain ⟨c1, b, hc1, e1, r1, f1⟩ := add_pair 104 120 121 (by omega) (by omega) (by omega)
    input tape d.width row.val.bits (d.outputBases 0) (d.outputBases 1) d.clock
    (outputWords d j.val 0) (outputWords d j.val 1) row d.width_nonempty
    (addressValue_bits _) d.clock_length B 0 0 hd.1 hd.2.1 hi0
    (hd.2.2.2.2.2 0) (hd.2.2.2.2.2 1) (by simp) (by simp) a r0 data0.width i0
    (data0.outputBases 0) (data0.outputBases 1) data0.clock (data0.outputs 0) (data0.outputs 1)
  have hreadp := outputWords_value d j.val row 0 hpfit hnfit
  have hreadn := outputWords_value d j.val row 1 hpfit hnfit
  simp only [zero_add, hreadp, hreadn, true_or, ite_true, Fin.isValue] at r1
  change Ready b.val (dotValues p q) at r1
  have data1 := data0.of_step f1
  obtain ⟨c2, c, hc2, e2, r2, f2⟩ := add_pair 102 161 162 (by omega) (by omega) (by omega)
    input tape d.width index (d.inputBases 1) (d.inputBases 2) d.clock
    (d.inputWords 1) (d.inputWords 2) j d.width_nonempty hindex d.clock_length B p q
    hd.1 hd.2.1 hilen (hd.2.2.2.2.1 1) (hd.2.2.2.2.1 2)
    (hpfit.trans hd.2.1) (hnfit.trans hd.2.1) b r1 data1.width
    (Affine.frame_word f1 _ (by omega) index0) (data1.inputBases 1) (data1.inputBases 2)
    data1.clock (data1.inputs 1) (data1.inputs 2)
  have data2 := data1.of_step f2
  have f12 := f1.trans f2
  have index2 := Affine.frame_word f12 _ (by omega) i0
  have blank2 := RationalAccumulator.blank_of_eq
    (f12.2.2.2.2.1 37 (by omega) (by omega)) blank0
  obtain ⟨c3, t, hc3, e3, r3, blank3, data3, f3, out3⟩ := write_four d (outputWords d j.val)
    B hd row (p+d.records.positive j) (q+d.records.negative j) hnextp hnextn
    input tape row.val.bits (addressValue_bits _) hi0 c r2 data2 index2 blank2
  rw [outputWords_step] at data3
  have ff0 : MatrixFrame s.val a.val :=
    ⟨f0.1, f0.2.1, f0.2.2.1, fun i hi _ _ _ _ h104 _ _ => f0.2.2.2.1 i hi h104,
      f0.2.2.2.2⟩
  refine ⟨c0+(c1+(c2+c3)), t, by omega, e0.seq (e1.seq (e2.seq e3)), r3, data3,
    BankArray.word_of_eq (f3.2.2.2.1 104 (by omega) (by omega) (by omega) (by omega)) index2,
    hi0, blank3, (ff0.trans (MatrixFrame.of_loop (LoopFrame.of_step f12))).trans
      (MatrixFrame.of_row f3), (Outside.of_memory (f12.1.trans hm0)).trans out3, ?_⟩
  intro i hi
  exact (f3.2.2.2.1 i (by omega) (by omega) (by omega) (by omega)).trans
    ((f12.2.2.2.2.1 i (by omega) (by omega)).trans
      (f0.2.2.2.1 i (by omega) (by omega)))

end Maxwell.Cost.CalibrationMatrix.SourceInit
