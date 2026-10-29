import Maxwell.Cost.CalibrationMatrix.Affine.Row
import Maxwell.Cost.CalibrationMatrix.Affine.Fill

namespace Maxwell.Cost.CalibrationMatrix.Affine
open Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 1500000
variable {n : ℕ}

def Invariant (d : Data n) (words : Fin 10 → Vector (List Bool) n)
    (B : ℕ) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ n ∧ ∃ index : List Bool,
    addressValue index = n-remaining ∧ index.length ≤ B ∧ BankArray.Word s.val 104 index ∧
    Stored d (filledWords d words (n-remaining)) s.val ∧ Ready s.val (dotValues 0 0) ∧
    Blank s.val 37 ∧ (∀ j, j = 102 ∨ j = 103 ∨ j = 106 → s.val.tapes j = initial.tapes j) ∧
    MatrixFrame initial s.val ∧ Outside d initial s.val

theorem invariant_stable (d : Data n) (words : Fin 10 → Vector (List Bool) n)
    (B : ℕ) (initial : BitRAMState) (remaining : ℕ) (s t : Store)
    (hf : CountedShifted.Frame 108 s t) (hs : Invariant d words B initial remaining s) :
    Invariant d words B initial remaining t := by
  obtain ⟨hr, i, hi, hil, hindex, hd, hw, h37, hctrl, hfr, hmem⟩ := hs
  have frame := MatrixFrame.of_counter hf
  have hm := hf.2.2.1
  have keep := hf.2.2.2.2.2.1
  exact ⟨hr, i, hi, hil, BankArray.word_of_eq (keep 104 (by omega)) hindex,
    hd.of_tapes_memory hm (fun j hj => keep j (by omega)),
    hw.of_tapes (fun j hj => keep j (by omega)),
    RationalAccumulator.blank_of_eq (keep 37 (by omega)) h37,
    (fun j hj => (keep j (by omega)).trans (hctrl j hj)), hfr.trans frame, hmem.trans (Outside.of_memory hm)⟩

def code : Code := .seq (CountedShifted.code 108 rowCode) (.call (TapeOps.clear 108))
def costBound (n B : ℕ) : ℕ := (n+1)*(13*B+15)+n*(2000000*(B+2)^2)+6*B+4

theorem executes (d : Data n) (words : Fin 10 → Vector (List Bool) n) (B : ℕ)
    (hd : d.Sized B) (hn : n < 2^B)
    (hwp : ∀ i, (newWPositive d words i).bits.length ≤ addressValue d.width)
    (hwn : ∀ i, (newWNegative d words i).bits.length ≤ addressValue d.width)
    (hxp : ∀ i, (newXPositive d words i).bits.length ≤ addressValue d.width)
    (hxn : ∀ i, (newXNegative d words i).bits.length ≤ addressValue d.width)
    (input : List Bool) (tape : ℕ → Bool) (index count : List Bool)
    (hi : addressValue index = 0) (hc : addressValue count = n)
    (hil : index.length ≤ B) (hcl : count.length ≤ B) (origin : ℤ) (s : Store)
    (hr : Ready s.val (dotValues 0 0)) (hdata : Stored d words s.val)
    (hindex : BankArray.Word s.val 104 index) (h37 : Blank s.val 37)
    (h108 : s.val.tapes 108 = BitTape.shifted count origin) :
    ∃ steps, ∃ t : Store, ∃ finalIndex : List Bool,
      steps ≤ costBound n B ∧ Executes input tape code steps s t ∧
      addressValue finalIndex = n ∧ finalIndex.length ≤ B ∧ BankArray.Word t.val 104 finalIndex ∧
      Stored d (filledWords d words n) t.val ∧ Ready t.val (dotValues 0 0) ∧
      Blank t.val 37 ∧ Blank t.val 108 ∧
      (∀ j, j = 102 ∨ j = 103 ∨ j = 106 → t.val.tapes j = s.val.tapes j) ∧
      MatrixFrame s.val t.val ∧ Outside d s.val t.val := by
  let inv := Invariant d words B s.val
  have stable : ∀ r a b, CountedShifted.Frame 108 a b → inv r a → inv r b :=
    invariant_stable d words B s.val
  have bodyCorrect : ∀ r xs u, inv (r+1) u →
      u.val.tapes 108 = BitTape.shifted xs origin → addressValue xs = r →
      ∃ bodyCost t, Executes input tape rowCode bodyCost u t ∧ inv r t ∧
        t.val.tapes 108 = BitTape.shifted xs origin ∧ bodyCost ≤ 2000000*(B+2)^2 := by
    intro r xs u hu hcounter _
    obtain ⟨hrem, idx, hidx, hidxl, hui, hud, hur, hu37, huc, huf, hum⟩ := hu
    let i : Fin n := ⟨n-(r+1), by omega⟩
    obtain ⟨steps, t, hsteps, he, htr, htd, hti, htil, ht37, ht108, htm, htc, htf⟩ :=
      row d (filledWords d words (n-(r+1))) B hd hn i
        (by simpa using hwp i) (by simpa using hwn i) (by simpa using hxp i) (by simpa using hxn i)
        input tape idx hidx hidxl u hur hud hui hu37
    have hnext : n-r = i.val+1 := by dsimp [i]; omega
    have hnextData : Stored d (filledWords d words (n-r)) t.val := by
      rw [hnext, ← filledWords_step d words i]
      exact htd
    refine ⟨steps, t, he, ⟨by omega, Increment.bits idx, ?_, htil, hti, hnextData,
      htr, ht37, (fun j hj => (htc j hj).trans (huc j hj)), huf.trans htf, hum.trans (Outside.of_row i htm)⟩,
      ht108.trans hcounter, hsteps⟩
    rw [Increment.bits_value, hidx]
    dsimp [i] at hnext
    omega
  have hinitial : inv n s := by
    refine ⟨le_rfl, index, by simpa using hi, hil, hindex, ?_, hr, h37, (fun _ _ => rfl),
      MatrixFrame.refl s.val, Outside.refl d s.val⟩
    simpa using hdata
  obtain ⟨steps, a, finalCount, he, haInv, haCount, haLen, _, haCost⟩ :=
    CountedShifted.executes 108 origin rowCode input tape inv (fun _ => 2000000*(B+2)^2)
      stable bodyCorrect n count s hc h108 hinitial
  obtain ⟨_, fi, hfi, hfil, hai, had, har, ha37, hac, haf, ham⟩ := haInv
  obtain ⟨t, et, ht, ft⟩ := WordCall.clear 108 input tape finalCount origin a haCount
  have keep (i : ℕ) (hi : i ≠ 108) : t.val.tapes i = a.val.tapes i := by simp [ht, hi]
  have frame : MatrixFrame a.val t.val :=
    ⟨ft.2.1, ft.2.2.2.1, ft.2.2.2.2.1, fun i _ _ _ _ _ _ _ h108 => keep i h108,
      fun i _ _ _ h26 h27 _ _ => ft.2.2.2.2.2.2 i h26 h27⟩
  refine ⟨steps+(6*finalCount.length+4), t, fi, ?_, he.seq et,
    by simpa using hfi, hfil, BankArray.word_of_eq (keep 104 (by omega)) hai,
    ?_, har.of_tapes (fun i hi => keep i (by omega)),
    RationalAccumulator.blank_of_eq (keep 37 (by omega)) ha37,
    ⟨origin+finalCount.length, by simp [ht]⟩,
    (fun j hj => (keep j (by omega)).trans (hac j hj)), haf.trans frame, ham.trans (Outside.of_memory ft.2.2.1)⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at haCost
    have hlen : finalCount.length ≤ B := haLen.trans_le hcl
    have hcounter : (n+1)*(13*count.length+15) ≤ (n+1)*(13*B+15) := by gcongr
    dsimp [costBound]
    omega
  · simpa using had.of_tapes_memory ft.2.2.1 (fun i hi => keep i (by omega))

theorem costBound_le (n B : ℕ) : costBound n B ≤ 2100000*(n+1)*(B+2)^2 := by
  unfold costBound
  have hquad : B+2 ≤ (B+2)^2 := by nlinarith
  nlinarith

end Maxwell.Cost.CalibrationMatrix.Affine
