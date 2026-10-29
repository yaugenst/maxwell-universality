import Maxwell.Cost.CalibrationMatrix.SourceInit.Scatter

namespace Maxwell.Cost.CalibrationMatrix.SourceInit

open Structured
open RationalAccumulator (Blank)
open scoped BigOperators

theorem increment_cursor {m n : ℕ} (d : Data m n) (words : Fin 4 → Vector (List Bool) n)
    (bank : ℕ) (hbank : bank = 102 ∨ bank = 104) (input : List Bool) (tape : ℕ → Bool)
    (index : List Bool) (B : ℕ) (hilen : index.length ≤ B) (hnext : addressValue index+1 < 2^B)
    (s : Store) (hready : Ready s.val (dotValues 0 0)) (hdata : Stored d words s.val)
    (hindex : BankArray.Word s.val bank index) (h37 : Blank s.val 37) :
    ∃ cost t, cost ≤ 12*B+18 ∧ Executes input tape (BankArray.incrementCode bank) cost s t ∧
      Ready t.val (dotValues 0 0) ∧ Stored d words t.val ∧
      BankArray.Word t.val bank (Increment.bits index) ∧ (Increment.bits index).length ≤ B ∧
      Blank t.val 37 ∧ MatrixFrame s.val t.val ∧ t.val.memory = s.val.memory ∧
      (∀ i, i ≠ bank → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨cost, t, hc, he, hi, _, hm, _, ht, hf⟩ := BankArray.increment_bank bank (by omega)
    input tape index s hindex hready.2.1
  refine ⟨cost, t, by omega, he, hready.of_tapes (fun i hi => ht i (by omega)),
    hdata.of_tapes_memory hm (fun i hi => ht i (by omega)), hi,
    BankArray.increment_length_bound index B hilen hnext,
    RationalAccumulator.blank_of_eq (ht 37 (by omega)) h37, ?_, hm, ht⟩
  exact ⟨hf.1, hf.2.1, hf.2.2.1,
    fun i hi _ _ h102 _ h104 _ _ => hf.2.2.2.1 i hi (by omega), hf.2.2.2.2⟩

def zeroRowCode : Code := .seq writeCode (BankArray.incrementCode 104)
def scatterRowCode : Code := .seq scatterCode (BankArray.incrementCode 102)

theorem zero_row {m n : ℕ} (d : Data m n) (initial : Fin 4 → Vector (List Bool) n)
    (B : ℕ) (hd : d.Sized B) (hn : n < 2^B) (row : Fin n)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hindex : addressValue index = row.val) (hilen : index.length ≤ B)
    (s : Store) (hready : Ready s.val (dotValues 0 0))
    (hdata : Stored d (zeroWords d initial row.val) s.val)
    (h104 : BankArray.Word s.val 104 index) (h37 : Blank s.val 37) :
    ∃ cost t, cost ≤ 171000*(B+2)^2 ∧ Executes input tape zeroRowCode cost s t ∧
      Ready t.val (dotValues 0 0) ∧ Stored d (zeroWords d initial (row.val+1)) t.val ∧
      BankArray.Word t.val 104 (Increment.bits index) ∧ (Increment.bits index).length ≤ B ∧
      Blank t.val 37 ∧ MatrixFrame s.val t.val ∧ Outside d s.val t.val ∧
      (∀ i, i = 102 ∨ i = 103 ∨ i = 106 ∨ i = 108 → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨c1, a, hc1, e1, r1, b1, data1, f1, out1⟩ := write_four d
    (zeroWords d initial row.val) B hd row 0 0 (by simp) (by simp)
    input tape index hindex hilen s hready hdata h104 h37
  rw [zeroWords_step] at data1
  have i1 := BankArray.word_of_eq (f1.2.2.2.1 104 (by omega) (by omega) (by omega) (by omega)) h104
  obtain ⟨c2, t, hc2, e2, r2, data2, i2, hi2, b2, f2, hm2, ht2⟩ := increment_cursor
    d (zeroWords d initial (row.val+1)) 104 (by omega) input tape index B hilen
    (by omega) a r1 data1 i1 b1
  refine ⟨c1+c2, t, ?_, e1.seq e2, r2, data2, i2, hi2, b2,
    (MatrixFrame.of_row f1).trans f2, out1.trans (Outside.of_memory hm2), ?_⟩
  · have hsq : B+2 ≤ (B+2)^2 := Nat.le_self_pow (by decide) _
    clear * - hc1 hc2 hsq
    omega
  · intro i hi
    exact (ht2 i (by omega)).trans (f1.2.2.2.1 i (by omega) (by omega) (by omega) (by omega))

theorem scatter_row {m n : ℕ} (d : Data m n) (B : ℕ) (hd : d.Sized B) (hm : m < 2^B)
    (hp : (∑ j, d.records.positive j).bits.length ≤ addressValue d.width)
    (hn : (∑ j, d.records.negative j).bits.length ≤ addressValue d.width)
    (j : Fin m) (input : List Bool) (tape : ℕ → Bool) (index old : List Bool)
    (hindex : addressValue index = j.val) (hilen : index.length ≤ B) (holen : old.length ≤ B)
    (s : Store) (hready : Ready s.val (dotValues 0 0))
    (hdata : Stored d (outputWords d j.val) s.val)
    (h102 : BankArray.Word s.val 102 index) (h104 : BankArray.Word s.val 104 old) (h37 : Blank s.val 37) :
    ∃ cost t, cost ≤ 292000*(B+2)^2 ∧ Executes input tape scatterRowCode cost s t ∧
      Ready t.val (dotValues 0 0) ∧ Stored d (outputWords d (j.val+1)) t.val ∧
      BankArray.Word t.val 102 (Increment.bits index) ∧ (Increment.bits index).length ≤ B ∧
      BankArray.Word t.val 104 (d.records.index j).val.bits ∧
      (d.records.index j).val.bits.length ≤ B ∧ Blank t.val 37 ∧
      MatrixFrame s.val t.val ∧ Outside d s.val t.val ∧
      (∀ i, i = 103 ∨ i = 106 ∨ i = 108 → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨c1, a, hc1, e1, r1, data1, i104, hi104, b1, f1, out1, ht1⟩ :=
    scatter d B hd hp hn j input tape index old hindex hilen holen s hready hdata h102 h104 h37
  have i1 := BankArray.word_of_eq (ht1 102 (by omega)) h102
  obtain ⟨c2, t, hc2, e2, r2, data2, i2, hi2, b2, f2, hm2, ht2⟩ := increment_cursor
    d (outputWords d (j.val+1)) 102 (by omega) input tape index B hilen
    (by omega) a r1 data1 i1 b1
  refine ⟨c1+c2, t, ?_, e1.seq e2, r2, data2, i2, hi2,
    BankArray.word_of_eq (ht2 104 (by omega)) i104, hi104, b2, f1.trans f2,
    out1.trans (Outside.of_memory hm2), ?_⟩
  · have hsq : B+2 ≤ (B+2)^2 := Nat.le_self_pow (by decide) _
    clear * - hc1 hc2 hsq
    omega
  · intro i hi
    exact (ht2 i (by omega)).trans (ht1 i (by omega))

end Maxwell.Cost.CalibrationMatrix.SourceInit
