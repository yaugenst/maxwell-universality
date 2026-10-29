import Maxwell.Cost.CalibrationMatrix.SourceInit.Iteration

namespace Maxwell.Cost.CalibrationMatrix.SourceInit

open Structured
open RationalAccumulator (Blank)
open scoped BigOperators

namespace ScatterPass

def Invariant {m n : ℕ} (d : Data m n) (B : ℕ) (initial : BitRAMState)
    (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ m ∧ ∃ index old : List Bool,
    addressValue index = m-remaining ∧ index.length ≤ B ∧ old.length ≤ B ∧
    BankArray.Word s.val 102 index ∧ BankArray.Word s.val 104 old ∧
    Stored d (outputWords d (m-remaining)) s.val ∧ Ready s.val (dotValues 0 0) ∧
    Blank s.val 37 ∧ (∀ i, i = 103 ∨ i = 108 → s.val.tapes i = initial.tapes i) ∧
    MatrixFrame initial s.val ∧ Outside d initial s.val

theorem invariant_stable {m n : ℕ} (d : Data m n) (B : ℕ) (initial : BitRAMState)
    (remaining : ℕ) (s t : Store) (hf : CountedShifted.Frame 106 s t)
    (hs : Invariant d B initial remaining s) : Invariant d B initial remaining t := by
  obtain ⟨hr, i, old, hi, hil, hol, h102, h104, hd, hw, h37, hctrl, hfr, hmem⟩ := hs
  have frame := MatrixFrame.of_loop (LoopFrame.of_counter hf)
  have hm := hf.2.2.1
  have keep := hf.2.2.2.2.2.1
  exact ⟨hr, i, old, hi, hil, hol, BankArray.word_of_eq (keep 102 (by omega)) h102,
    BankArray.word_of_eq (keep 104 (by omega)) h104,
    hd.of_tapes_memory hm (fun j hj => keep j (by omega)),
    hw.of_tapes (fun j hj => keep j (by omega)),
    RationalAccumulator.blank_of_eq (keep 37 (by omega)) h37,
    (fun j hj => (keep j (by omega)).trans (hctrl j hj)), hfr.trans frame, hmem.trans (Outside.of_memory hm)⟩

def code : Code := .seq (CountedShifted.code 106 scatterRowCode) (.call (TapeOps.clear 106))
def costBound (m B : ℕ) : ℕ := (m+1)*(13*B+15)+m*(292000*(B+2)^2)+6*B+4

theorem executes {m n : ℕ} (d : Data m n) (B : ℕ) (hd : d.Sized B) (hm : m < 2^B)
    (hp : (∑ j, d.records.positive j).bits.length ≤ addressValue d.width)
    (hn : (∑ j, d.records.negative j).bits.length ≤ addressValue d.width)
    (input : List Bool) (tape : ℕ → Bool) (index old count : List Bool)
    (hi : addressValue index = 0) (hc : addressValue count = m)
    (hil : index.length ≤ B) (hol : old.length ≤ B) (hcl : count.length ≤ B)
    (origin : ℤ) (s : Store) (hr : Ready s.val (dotValues 0 0))
    (hdata : Stored d (outputWords d 0) s.val)
    (h102 : BankArray.Word s.val 102 index) (h104 : BankArray.Word s.val 104 old)
    (h37 : Blank s.val 37) (h106 : s.val.tapes 106 = BitTape.shifted count origin) :
    ∃ steps, ∃ t : Store, ∃ finalIndex finalTarget : List Bool,
      steps ≤ costBound m B ∧ Executes input tape code steps s t ∧
      addressValue finalIndex = m ∧ finalIndex.length ≤ B ∧ finalTarget.length ≤ B ∧
      BankArray.Word t.val 102 finalIndex ∧ BankArray.Word t.val 104 finalTarget ∧
      Stored d (outputWords d m) t.val ∧ Ready t.val (dotValues 0 0) ∧
      Blank t.val 37 ∧ Blank t.val 106 ∧
      (∀ j, j = 103 ∨ j = 108 → t.val.tapes j = s.val.tapes j) ∧
      MatrixFrame s.val t.val ∧ Outside d s.val t.val := by
  let inv := Invariant d B s.val
  have stable : ∀ r a b, CountedShifted.Frame 106 a b → inv r a → inv r b :=
    invariant_stable d B s.val
  have bodyCorrect : ∀ r xs u, inv (r+1) u →
      u.val.tapes 106 = BitTape.shifted xs origin → addressValue xs = r →
      ∃ bodyCost t, Executes input tape scatterRowCode bodyCost u t ∧ inv r t ∧
        t.val.tapes 106 = BitTape.shifted xs origin ∧ bodyCost ≤ 292000*(B+2)^2 := by
    intro r xs u hu hcounter _
    obtain ⟨hrem, idx, old, hidx, hidxl, hold, hui, hut, hud, hur, hu37, huc, huf, hum⟩ := hu
    let j : Fin m := ⟨m-(r+1), by omega⟩
    obtain ⟨steps, t, hsteps, he, htr, htd, hti, htil, htt, httl, ht37, htf, htm, htc⟩ :=
      scatter_row d B hd hm hp hn j input tape idx old hidx hidxl hold u hur hud hui hut hu37
    have hnext : m-r = j.val+1 := by dsimp [j]; omega
    refine ⟨steps, t, he, ⟨by omega, Increment.bits idx, (d.records.index j).val.bits,
      ?_, htil, httl, hti, htt, hnext ▸ htd, htr, ht37,
      (fun j hj => (htc j (by omega)).trans (huc j hj)), huf.trans htf, hum.trans htm⟩,
      (htc 106 (by omega)).trans hcounter, hsteps⟩
    rw [Increment.bits_value, hidx]
    dsimp [j] at hnext
    omega
  have hinitial : inv m s := by
    refine ⟨le_rfl, index, old, by simpa using hi, hil, hol, h102, h104, ?_, hr, h37,
      (fun _ _ => rfl), MatrixFrame.refl s.val, Outside.refl d s.val⟩
    simpa using hdata
  obtain ⟨steps, a, finalCount, he, haInv, haCount, haLen, _, haCost⟩ :=
    CountedShifted.executes 106 origin scatterRowCode input tape inv (fun _ => 292000*(B+2)^2)
      stable bodyCorrect m count s hc h106 hinitial
  obtain ⟨_, fi, target, hfi, hfil, htl, hai, hat, had, har, ha37, hac, haf, ham⟩ := haInv
  obtain ⟨t, et, ht, ft⟩ := WordCall.clear 106 input tape finalCount origin a haCount
  have keep (i : ℕ) (hi : i ≠ 106) : t.val.tapes i = a.val.tapes i := by simp [ht, hi]
  have frame : MatrixFrame a.val t.val :=
    ⟨ft.2.1, ft.2.2.2.1, ft.2.2.2.2.1, fun i _ _ _ _ _ _ h106 _ => keep i h106,
      fun i _ _ _ h26 h27 _ _ => ft.2.2.2.2.2.2 i h26 h27⟩
  refine ⟨steps+(6*finalCount.length+4), t, fi, target, ?_, he.seq et,
    by simpa using hfi, hfil, htl, BankArray.word_of_eq (keep 102 (by omega)) hai,
    BankArray.word_of_eq (keep 104 (by omega)) hat, ?_,
    har.of_tapes (fun i hi => keep i (by omega)),
    RationalAccumulator.blank_of_eq (keep 37 (by omega)) ha37,
    ⟨origin+finalCount.length, by simp [ht]⟩,
    (fun j hj => (keep j (by omega)).trans (hac j hj)), haf.trans frame, ham.trans (Outside.of_memory ft.2.2.1)⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at haCost
    have hlen : finalCount.length ≤ B := haLen.trans_le hcl
    have hcounter : (m+1)*(13*count.length+15) ≤ (m+1)*(13*B+15) := by gcongr
    dsimp [costBound]
    omega
  · simpa only [Nat.sub_zero] using
      had.of_tapes_memory ft.2.2.1 (fun i hi => keep i (by omega))

theorem costBound_le (m B : ℕ) : costBound m B ≤ 293000*(m+1)*(B+2)^2 := by
  unfold costBound
  have hquad : B+2 ≤ (B+2)^2 := by nlinarith
  nlinarith

end ScatterPass
end Maxwell.Cost.CalibrationMatrix.SourceInit
