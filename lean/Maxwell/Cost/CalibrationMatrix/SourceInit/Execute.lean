import Maxwell.Cost.CalibrationMatrix.SourceInit.ZeroPass
import Maxwell.Cost.CalibrationMatrix.SourceInit.ScatterPass
import Maxwell.Cost.CalibrationMatrix.SourceInit.Control

namespace Maxwell.Cost.CalibrationMatrix.SourceInit

open Structured
open RationalAccumulator (Blank)
open scoped BigOperators

set_option maxHeartbeats 1200000

/-- Fixed code: clone the dense dimension, zero the outputs, clone the sparse
record count, scatter actual records, and reclaim both cursors. -/
def code : Code := .seq (Assign.code 107 108)
  (.seq ZeroPass.code (.seq (Assign.code 159 106)
    (.seq ScatterPass.code (.seq (.call (TapeOps.clear 102)) (.call (TapeOps.clear 104))))))

def costBound (m n B : ℕ) : ℕ := 1000000*(m+n+1)*(B+2)^2

theorem executes {m n : ℕ} (d : Data m n) (initial : Fin 4 → Vector (List Bool) n)
    (B : ℕ) (hd : d.Sized B) (hm : m < 2^B) (hn : n < 2^B)
    (hp : (∑ j, d.records.positive j).bits.length ≤ addressValue d.width)
    (hq : (∑ j, d.records.negative j).bits.length ≤ addressValue d.width)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hready : Ready s.val (dotValues 0 0)) (hdata : Stored d initial s.val)
    (h102 : BankArray.Word s.val 102 []) (h103 : BankArray.Word s.val 103 [])
    (h104 : BankArray.Word s.val 104 []) (h37 : Blank s.val 37)
    (h106 : Blank s.val 106) (h108 : Blank s.val 108) :
    ∃ steps t, steps ≤ costBound m n B ∧ Executes input tape code steps s t ∧
      Stored d (outputWords d m) t.val ∧ Ready t.val (dotValues 0 0) ∧
      BankArray.Word t.val 102 [] ∧ BankArray.Word t.val 103 [] ∧ BankArray.Word t.val 104 [] ∧
      Blank t.val 37 ∧ Blank t.val 106 ∧ Blank t.val 108 ∧
      MatrixFrame s.val t.val ∧ Outside d s.val t.val := by
  obtain ⟨a, e1, r1, data1, count1, f1, hm1, ht1⟩ := load_count d initial 107 108
    (by omega) (by omega) (by omega) input tape d.dimension s hready hdata hdata.dimension h108
  obtain ⟨origin1, hcount1⟩ := count1
  obtain ⟨c2, b, firstTarget, hc2, e2, _, hlen2, i1042, data2, r2, b372, b1082, ht2, f2, out2⟩ :=
    ZeroPass.executes d initial B hd hn input tape [] d.dimension (by rfl) d.dimension_value
      (by simp) hd.2.2.1 origin1 a r1 data1
      (BankArray.word_of_eq (ht1 104 (by omega)) h104)
      (RationalAccumulator.blank_of_eq (ht1 37 (by omega)) h37) hcount1
  have blank1062 := RationalAccumulator.blank_of_eq
    ((ht2 106 (by omega)).trans (ht1 106 (by omega))) h106
  have index1022 := BankArray.word_of_eq
    ((ht2 102 (by omega)).trans (ht1 102 (by omega))) h102
  have index1032 := BankArray.word_of_eq
    ((ht2 103 (by omega)).trans (ht1 103 (by omega))) h103
  obtain ⟨c, e3, r3, data3, count3, f3, hm3, ht3⟩ := load_count d (outputWords d 0) 159 106
    (by omega) (by omega) (by omega) input tape d.count b r2 data2 data2.count blank1062
  obtain ⟨origin3, hcount3⟩ := count3
  obtain ⟨c4, e, finalIndex, finalTarget, hc4, e4, _, hlen4, htlen4, i1024, i1044,
    data4, r4, b374, b1064, ht4, f4, out4⟩ := ScatterPass.executes d B hd hm hp hq
    input tape [] firstTarget d.count (by rfl) d.count_value (by simp) hlen2 hd.2.2.2.1
    origin3 c r3 data3 (BankArray.word_of_eq (ht3 102 (by omega)) index1022)
    (BankArray.word_of_eq (ht3 104 (by omega)) i1042)
    (RationalAccumulator.blank_of_eq (ht3 37 (by omega)) b372) hcount3
  have index1034 := BankArray.word_of_eq
    ((ht4 103 (by omega)).trans (ht3 103 (by omega))) index1032
  have blank1084 := RationalAccumulator.blank_of_eq
    ((ht4 108 (by omega)).trans (ht3 108 (by omega))) b1082
  obtain ⟨f, e5, r5, data5, i1025, f5, hm5, ht5⟩ := clear_cursor d (outputWords d m)
    102 (by omega) input tape finalIndex e r4 data4 i1024
  obtain ⟨t, e6, r6, data6, i1046, f6, hm6, ht6⟩ := clear_cursor d (outputWords d m)
    104 (by omega) input tape finalTarget f r5 data5
    (BankArray.word_of_eq (ht5 104 (by omega)) i1044)
  have keep (i : ℕ) (hi : i ≠ 102) (hj : i ≠ 104) : t.val.tapes i = e.val.tapes i :=
    (ht6 i hj).trans (ht5 i hi)
  refine ⟨15*d.dimension.length+21+(c2+(15*d.count.length+21+
      (c4+(6*finalIndex.length+4+(6*finalTarget.length+4))))), t, ?_,
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6)))), data6, r6,
    BankArray.word_of_eq (ht6 102 (by omega)) i1025,
    BankArray.word_of_eq (keep 103 (by omega) (by omega)) index1034, i1046,
    RationalAccumulator.blank_of_eq (keep 37 (by omega) (by omega)) b374,
    RationalAccumulator.blank_of_eq (keep 106 (by omega) (by omega)) b1064,
    RationalAccumulator.blank_of_eq (keep 108 (by omega) (by omega)) blank1084,
    ((((f1.trans f2).trans f3).trans f4).trans f5).trans f6,
    ((((Outside.of_memory hm1).trans out2).trans (Outside.of_memory hm3)).trans out4).trans
      (Outside.of_memory (hm6.trans hm5))⟩
  have hzero := hc2.trans (ZeroPass.costBound_le n B)
  have hscatter := hc4.trans (ScatterPass.costBound_le m B)
  have hdim := hd.2.2.1
  have hcount := hd.2.2.2.1
  have hsq : B+2 ≤ (B+2)^2 := Nat.le_self_pow (by decide) _
  unfold costBound
  clear * - hzero hscatter hdim hcount hlen4 htlen4 hsq
  nlinarith

/-- The compiled instruction stream has the same signed-array result and
an explicit polynomial upper bound on all charged BitRAM steps. -/
theorem run {m n : ℕ} (d : Data m n) (initial : Fin 4 → Vector (List Bool) n)
    (B : ℕ) (hd : d.Sized B) (hm : m < 2^B) (hn : n < 2^B)
    (hp : (∑ j, d.records.positive j).bits.length ≤ addressValue d.width)
    (hq : (∑ j, d.records.negative j).bits.length ≤ addressValue d.width)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hready : Ready s.val (dotValues 0 0)) (hdata : Stored d initial s.val)
    (h102 : BankArray.Word s.val 102 []) (h103 : BankArray.Word s.val 103 [])
    (h104 : BankArray.Word s.val 104 []) (h37 : Blank s.val 37)
    (h106 : Blank s.val 106) (h108 : Blank s.val 108) :
    ∃ t : Store, (runPriced (code.compile.next input tape) (costBound m n B+1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costBound m n B+1) s.val).instructions ≤
        costBound m n B ∧
      Stored d (outputWords d m) t.val ∧ Ready t.val (dotValues 0 0) ∧
      BankArray.Word t.val 102 [] ∧ BankArray.Word t.val 103 [] ∧ BankArray.Word t.val 104 [] ∧
      Blank t.val 37 ∧ Blank t.val 106 ∧ Blank t.val 108 ∧
      MatrixFrame s.val t.val ∧ Outside d s.val t.val := by
  obtain ⟨steps, t, hsteps, he, ht⟩ := executes d initial B hd hm hn hp hq input tape s
    hready hdata h102 h103 h104 h37 h106 h108
  have hrun := he.compiled_run (costBound m n B+1) (by omega)
  exact ⟨t, hrun.1, hrun.2.symm ▸ hsteps, ht⟩

end Maxwell.Cost.CalibrationMatrix.SourceInit
