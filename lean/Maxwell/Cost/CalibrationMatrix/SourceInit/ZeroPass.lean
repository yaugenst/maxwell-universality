import Maxwell.Cost.CalibrationMatrix.SourceInit.Iteration

namespace Maxwell.Cost.CalibrationMatrix.SourceInit

open Structured
open RationalAccumulator (Blank)

namespace ZeroPass

def Invariant {m n : ℕ} (d : Data m n) (words : Fin 4 → Vector (List Bool) n)
    (B : ℕ) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ n ∧ ∃ index : List Bool,
    addressValue index = n-remaining ∧ index.length ≤ B ∧ BankArray.Word s.val 104 index ∧
    Stored d (zeroWords d words (n-remaining)) s.val ∧ Ready s.val (dotValues 0 0) ∧
    Blank s.val 37 ∧ (∀ i, i = 102 ∨ i = 103 ∨ i = 106 → s.val.tapes i = initial.tapes i) ∧
    MatrixFrame initial s.val ∧ Outside d initial s.val

theorem invariant_stable {m n : ℕ} (d : Data m n) (words : Fin 4 → Vector (List Bool) n)
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

def code : Code := .seq (CountedShifted.code 108 zeroRowCode) (.call (TapeOps.clear 108))
def costBound (n B : ℕ) : ℕ := (n+1)*(13*B+15)+n*(171000*(B+2)^2)+6*B+4

theorem executes {m n : ℕ} (d : Data m n) (words : Fin 4 → Vector (List Bool) n) (B : ℕ)
    (hd : d.Sized B) (hn : n < 2^B) (input : List Bool) (tape : ℕ → Bool)
    (index count : List Bool) (hi : addressValue index = 0) (hc : addressValue count = n)
    (hil : index.length ≤ B) (hcl : count.length ≤ B) (origin : ℤ) (s : Store)
    (hr : Ready s.val (dotValues 0 0)) (hdata : Stored d words s.val)
    (hindex : BankArray.Word s.val 104 index) (h37 : Blank s.val 37)
    (h108 : s.val.tapes 108 = BitTape.shifted count origin) :
    ∃ steps, ∃ t : Store, ∃ finalIndex : List Bool,
      steps ≤ costBound n B ∧ Executes input tape code steps s t ∧
      addressValue finalIndex = n ∧ finalIndex.length ≤ B ∧ BankArray.Word t.val 104 finalIndex ∧
      Stored d (outputWords d 0) t.val ∧ Ready t.val (dotValues 0 0) ∧
      Blank t.val 37 ∧ Blank t.val 108 ∧
      (∀ j, j = 102 ∨ j = 103 ∨ j = 106 → t.val.tapes j = s.val.tapes j) ∧
      MatrixFrame s.val t.val ∧ Outside d s.val t.val := by
  let inv := Invariant d words B s.val
  have stable : ∀ r a b, CountedShifted.Frame 108 a b → inv r a → inv r b :=
    invariant_stable d words B s.val
  have bodyCorrect : ∀ r xs u, inv (r+1) u →
      u.val.tapes 108 = BitTape.shifted xs origin → addressValue xs = r →
      ∃ bodyCost t, Executes input tape zeroRowCode bodyCost u t ∧ inv r t ∧
        t.val.tapes 108 = BitTape.shifted xs origin ∧ bodyCost ≤ 171000*(B+2)^2 := by
    intro r xs u hu hcounter _
    obtain ⟨hrem, idx, hidx, hidxl, hui, hud, hur, hu37, huc, huf, hum⟩ := hu
    let i : Fin n := ⟨n-(r+1), by omega⟩
    obtain ⟨steps, t, hsteps, he, htr, htd, hti, htil, ht37, htf, htm, htc⟩ :=
      zero_row d words B hd hn i input tape idx hidx hidxl u hur hud hui hu37
    have hnext : n-r = i.val+1 := by dsimp [i]; omega
    refine ⟨steps, t, he, ⟨by omega, Increment.bits idx, ?_, htil, hti,
      hnext ▸ htd, htr, ht37, (fun j hj => (htc j (by omega)).trans (huc j hj)),
      huf.trans htf, hum.trans htm⟩, (htc 108 (by omega)).trans hcounter, hsteps⟩
    rw [Increment.bits_value, hidx]
    dsimp [i] at hnext
    omega
  have hinitial : inv n s := by
    refine ⟨le_rfl, index, by simpa using hi, hil, hindex, ?_, hr, h37, (fun _ _ => rfl),
      MatrixFrame.refl s.val, Outside.refl d s.val⟩
    simpa using hdata
  obtain ⟨steps, a, finalCount, he, haInv, haCount, haLen, _, haCost⟩ :=
    CountedShifted.executes 108 origin zeroRowCode input tape inv (fun _ => 171000*(B+2)^2)
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
  · simpa only [Nat.sub_zero, zeroWords_full] using
      had.of_tapes_memory ft.2.2.1 (fun i hi => keep i (by omega))

theorem costBound_le (n B : ℕ) : costBound n B ≤ 172000*(n+1)*(B+2)^2 := by
  unfold costBound
  have hquad : B+2 ≤ (B+2)^2 := by nlinarith
  nlinarith

end ZeroPass
end Maxwell.Cost.CalibrationMatrix.SourceInit
