import Maxwell.Cost.CalibrationMatrix.Iteration
import Maxwell.Cost.CalibrationMatrix.Prefix

namespace Maxwell.Cost.CalibrationMatrix

open Structured
open scoped BigOperators

set_option maxHeartbeats 800000

def DotInvariant {m n : ℕ} (d : Data m n) (start : ℕ) (h : start+n ≤ m)
    (B : ℕ) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ n ∧ ∃ mi vi : List Bool,
    addressValue mi = start+(n-remaining) ∧ addressValue vi = n-remaining ∧
    mi.length ≤ B ∧ vi.length ≤ B ∧ Indices s.val mi vi ∧ Stored d s.val ∧
    Ready s.val (dotValues (partialSum (d.rowPositive start h) (n-remaining))
      (partialSum (d.rowNegative start h) (n-remaining))) ∧ LoopFrame initial s.val

theorem dot_invariant_stable {m n : ℕ} (d : Data m n) (start : ℕ) (h : start+n ≤ m)
    (B : ℕ) (initial : BitRAMState) (remaining : ℕ) (s t : Store)
    (hf : CountedShifted.Frame 106 s t) (hs : DotInvariant d start h B initial remaining s) :
    DotInvariant d start h B initial remaining t := by
  obtain ⟨hr, mi, vi, hmi, hvi, hml, hvl, his, hd, hw, hfr⟩ := hs
  have hloop := LoopFrame.of_counter hf
  exact ⟨hr, mi, vi, hmi, hvi, hml, hvl,
    ⟨BankArray.word_of_eq (hf.2.2.2.2.2.1 102 (by omega)) his.1,
      BankArray.word_of_eq (hf.2.2.2.2.2.1 103 (by omega)) his.2⟩,
    hd.of_loop hloop, hw.of_tapes (fun i hi => hf.2.2.2.2.2.1 i (by omega)), hfr.trans hloop⟩

def dotCode : Code := .seq (CountedShifted.code 106 iterationCode) (.call (TapeOps.clear 106))

def dotCost (n B countLength : ℕ) : ℕ :=
  (n+1)*(13*countLength+15) + n*(510000*(B+2)^2) + 6*countLength+4

/-- One uniform finite countdown computes a complete signed row dot product
from concrete memory arrays. Every indexed read, product, sum, increment,
loop test, and scratch cleanup is included in the polynomial charge. -/
theorem dot {m n : ℕ} (d : Data m n) (start B : ℕ) (hrow : start+n ≤ m)
    (hsized : d.Sized B) (hm : m < 2^B)
    (hp : (∑ j, d.rowPositive start hrow j).bits.length ≤ B)
    (hneg : (∑ j, d.rowNegative start hrow j).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (mi vi countWord : List Bool)
    (hmi : addressValue mi = start) (hvi : addressValue vi = 0)
    (hml : mi.length ≤ B) (hvl : vi.length ≤ B) (hcount : addressValue countWord = n)
    (countOrigin : ℤ) (s : Store) (hcountWord : s.val.tapes 106 = BitTape.shifted countWord countOrigin)
    (hready : Ready s.val (dotValues 0 0)) (hdata : Stored d s.val) (hindices : Indices s.val mi vi) :
    ∃ cost, ∃ t : Store, ∃ finalMatrixIndex finalVectorIndex : List Bool,
      cost ≤ dotCost n B countWord.length ∧ Executes input tape dotCode cost s t ∧
      addressValue finalMatrixIndex = start+n ∧ addressValue finalVectorIndex = n ∧
      finalMatrixIndex.length ≤ B ∧ finalVectorIndex.length ≤ B ∧
      Indices t.val finalMatrixIndex finalVectorIndex ∧ Stored d t.val ∧
      Ready t.val (dotValues (∑ j, d.rowPositive start hrow j) (∑ j, d.rowNegative start hrow j)) ∧
      RationalAccumulator.Blank t.val 106 ∧ LoopFrame s.val t.val := by
  let inv := DotInvariant d start hrow B s.val
  let bound := 510000*(B+2)^2
  have stable : ∀ r a b, CountedShifted.Frame 106 a b → inv r a → inv r b :=
    dot_invariant_stable d start hrow B s.val
  have bodyCorrect : ∀ r xs u, inv (r+1) u →
      u.val.tapes 106 = BitTape.shifted xs countOrigin → addressValue xs = r →
      ∃ bodyCost t, Executes input tape iterationCode bodyCost u t ∧
        inv r t ∧ t.val.tapes 106 = BitTape.shifted xs countOrigin ∧ bodyCost ≤ bound := by
    intro r xs u hu hcounter _
    obtain ⟨hr, midx, vidx, hmidx, hvidx, hmidxLen, hvidxLen, hidx, hdat, hwork, hfr⟩ := hu
    have hj : n-(r+1) < n := by omega
    let j : Fin n := ⟨n-(r+1), hj⟩
    let i : Fin m := rowIndex start hrow j
    obtain ⟨c, t, hc, he, htr, hti, htcount, htf⟩ := iteration d B hsized input tape midx vidx
      hmidxLen hvidxLen i j hmidx hvidx
      (partialSum (d.rowPositive start hrow) (n-(r+1)))
      (partialSum (d.rowNegative start hrow) (n-(r+1)))
      (partialSum_bits_le _ _ _ hp) (partialSum_bits_le _ _ _ hneg) u hwork hdat hidx
    have hnext : n-r = n-(r+1)+1 := by omega
    have hpnext : partialSum (d.rowPositive start hrow) (n-r) =
        partialSum (d.rowPositive start hrow) (n-(r+1)) + d.positiveTerm i j := by
      rw [hnext, partialSum_succ _ _ hj]
      rfl
    have hnnext : partialSum (d.rowNegative start hrow) (n-r) =
        partialSum (d.rowNegative start hrow) (n-(r+1)) + d.negativeTerm i j := by
      rw [hnext, partialSum_succ _ _ hj]
      rfl
    have hnewM : addressValue (Increment.bits midx) = start+(n-r) := by
      rw [Increment.bits_value, hmidx]; omega
    have hnewV : addressValue (Increment.bits vidx) = n-r := by
      rw [Increment.bits_value, hvidx]; omega
    have hlenM : (Increment.bits midx).length ≤ B :=
      BankArray.increment_length_bound midx B hmidxLen (by rw [hmidx]; omega)
    have hlenV : (Increment.bits vidx).length ≤ B :=
      BankArray.increment_length_bound vidx B hvidxLen (by rw [hvidx]; omega)
    refine ⟨c, t, he, ⟨by omega, Increment.bits midx, Increment.bits vidx,
      hnewM, hnewV, hlenM, hlenV, hti, hdat.of_loop htf, ?_, hfr.trans htf⟩,
      htcount.trans hcounter, hc⟩
    simpa only [hpnext, hnnext] using htr
  have hinitial : inv n s := by
    refine ⟨le_rfl, mi, vi, ?_, ?_, hml, hvl, hindices, hdata, ?_, LoopFrame.refl s.val⟩
    · simpa using hmi
    · simpa using hvi
    · simpa using hready
  obtain ⟨cost, r, finalCount, he, hrInv, hrCount, hrLen, _, hrCost⟩ :=
    CountedShifted.executes 106 countOrigin iterationCode input tape inv (fun _ => bound)
      stable bodyCorrect n countWord s hcount hcountWord hinitial
  obtain ⟨_, fm, fv, hfm, hfv, hfml, hfvl, hri, hrd, hrr, hrf⟩ := hrInv
  obtain ⟨t, ht, htapes, htf⟩ := WordCall.clear 106 input tape finalCount countOrigin r hrCount
  have keep (i : ℕ) (hi : i ≠ 106) : t.val.tapes i = r.val.tapes i := by simp [htapes, hi]
  have hloop : LoopFrame r.val t.val :=
    ⟨htf.2.2.1, htf.2.1, htf.2.2.2.1, htf.2.2.2.2.1,
      fun i _ _ _ _ hi => keep i hi,
      fun i _ _ _ h26 h27 _ _ => htf.2.2.2.2.2.2 i h26 h27⟩
  refine ⟨cost+(6*finalCount.length+4), t, fm, fv, ?_, he.seq ht,
    by simpa using hfm, by simpa using hfv, hfml, hfvl,
    ⟨BankArray.word_of_eq (keep 102 (by omega)) hri.1,
      BankArray.word_of_eq (keep 103 (by omega)) hri.2⟩,
    hrd.of_loop hloop, ?_, ⟨countOrigin+finalCount.length, by simp [htapes]⟩, hrf.trans hloop⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hrCost
    dsimp [dotCost, bound] at *
    omega
  · have hh := hrr.of_tapes (fun i hi => keep i (by omega))
    simpa using hh

theorem dot_compiled_run {m n : ℕ} (d : Data m n) (start B : ℕ) (hrow : start+n ≤ m)
    (hsized : d.Sized B) (hm : m < 2^B)
    (hp : (∑ j, d.rowPositive start hrow j).bits.length ≤ B)
    (hneg : (∑ j, d.rowNegative start hrow j).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (mi vi countWord : List Bool)
    (hmi : addressValue mi = start) (hvi : addressValue vi = 0)
    (hml : mi.length ≤ B) (hvl : vi.length ≤ B) (hcount : addressValue countWord = n)
    (countOrigin : ℤ) (s : Store) (hcountWord : s.val.tapes 106 = BitTape.shifted countWord countOrigin)
    (hready : Ready s.val (dotValues 0 0)) (hdata : Stored d s.val) (hindices : Indices s.val mi vi) :
    ∃ t : Store, ∃ finalMatrixIndex finalVectorIndex : List Bool,
      (runPriced (dotCode.compile.next input tape) (dotCost n B countWord.length+1) s.val).finished =
        some (t.place dotCode.size) ∧
      (runPriced (dotCode.compile.next input tape) (dotCost n B countWord.length+1) s.val).instructions ≤
        dotCost n B countWord.length ∧
      addressValue finalMatrixIndex = start+n ∧ addressValue finalVectorIndex = n ∧
      finalMatrixIndex.length ≤ B ∧ finalVectorIndex.length ≤ B ∧
      Indices t.val finalMatrixIndex finalVectorIndex ∧ Stored d t.val ∧
      Ready t.val (dotValues (∑ j, d.rowPositive start hrow j) (∑ j, d.rowNegative start hrow j)) ∧
      RationalAccumulator.Blank t.val 106 ∧ LoopFrame s.val t.val := by
  obtain ⟨cost, t, fi, fj, hc, he, ht⟩ := dot d start B hrow hsized hm hp hneg input tape
    mi vi countWord hmi hvi hml hvl hcount countOrigin s hcountWord hready hdata hindices
  have hr := he.compiled_run (dotCost n B countWord.length+1) (by omega)
  exact ⟨t, fi, fj, hr.1, hr.2 ▸ hc, ht⟩

end Maxwell.Cost.CalibrationMatrix
