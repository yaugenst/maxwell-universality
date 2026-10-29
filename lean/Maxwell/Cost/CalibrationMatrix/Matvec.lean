import Maxwell.Cost.CalibrationMatrix.Row
import Maxwell.Cost.CalibrationMatrix.Fill
import Maxwell.Cost.CalibrationMatrix.MemoryFrame

namespace Maxwell.Cost.CalibrationMatrix
open Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 1500000

theorem OutputStored.of_memory {rows : ℕ} {l : OutputLayout} {width : ℕ} {index : List Bool}
    {positive negative : Vector (List Bool) rows} {s t : BitRAMState}
    (h : OutputStored l width index positive negative s) (hm : t.memory = s.memory)
    (hk : ∀ i, i = 104 ∨ i = 114 ∨ i = 115 → t.tapes i = s.tapes i) :
    OutputStored l width index positive negative t :=
  ⟨BankArray.word_of_eq (hk 104 (by omega)) h.index,
    BankArray.word_of_eq (hk 114 (by omega)) h.positiveBase,
    BankArray.word_of_eq (hk 115 (by omega)) h.negativeBase,
    by simpa only [hm] using h.positive, by simpa only [hm] using h.negative⟩

def MatvecInvariant {rows n : ℕ} (d : Data (rows*n) n) (l : OutputLayout)
    (positive negative : Vector (List Bool) rows) (count : List Bool) (B : ℕ)
    (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ rows ∧ ∃ mi vi ri : List Bool,
    addressValue mi = (rows-remaining)*n ∧ addressValue vi = 0 ∧
    addressValue ri = rows-remaining ∧ mi.length ≤ B ∧ vi.length ≤ B ∧ ri.length ≤ B ∧
    Indices s.val mi vi ∧ Stored d s.val ∧ Ready s.val (dotValues 0 0) ∧
    OutputStored l (addressValue d.width) ri
      (fillPrefix positive d.positivePayload (rows-remaining))
      (fillPrefix negative d.negativePayload (rows-remaining)) s.val ∧
    BankArray.Word s.val 107 count ∧ Blank s.val 106 ∧ Blank s.val 37 ∧
    MatrixFrame initial s.val ∧ OutputOutside l rows (addressValue d.width) initial s.val

theorem matvec_invariant_stable {rows n : ℕ} (d : Data (rows*n) n) (l : OutputLayout)
    (positive negative : Vector (List Bool) rows) (count : List Bool) (B : ℕ)
    (initial : BitRAMState) (remaining : ℕ) (s t : Store)
    (hf : CountedShifted.Frame 108 s t)
    (hs : MatvecInvariant d l positive negative count B initial remaining s) :
    MatvecInvariant d l positive negative count B initial remaining t := by
  obtain ⟨hr, mi, vi, ri, hmi, hvi, hri, hml, hvl, hrl, hi, hd, hw, ho, hc, h106, h37, hfr, hmem⟩ := hs
  have frame := MatrixFrame.of_counter hf
  have hm := hf.2.2.1
  have keep := hf.2.2.2.2.2.1
  exact ⟨hr, mi, vi, ri, hmi, hvi, hri, hml, hvl, hrl,
    ⟨BankArray.word_of_eq (keep 102 (by omega)) hi.1,
      BankArray.word_of_eq (keep 103 (by omega)) hi.2⟩,
    hd.of_matrix hm frame, hw.of_tapes (fun i hi => keep i (by omega)),
    ho.of_memory hm (fun i hi => keep i (by omega)),
    BankArray.word_of_eq (keep 107 (by omega)) hc,
    RationalAccumulator.blank_of_eq (keep 106 (by omega)) h106,
    RationalAccumulator.blank_of_eq (keep 37 (by omega)) h37,
    hfr.trans frame, hmem.trans (OutputOutside.of_memory hm)⟩

def matvecCode : Code := .seq (CountedShifted.code 108 rowCode) (.call (TapeOps.clear 108))

def matvecCost (rows n B : ℕ) : ℕ :=
  (rows+1)*(13*B+15) + rows*rowCost n B + 6*B+4

/-- The fixed finite program runs the complete signed dense matrix-vector
product. Matrix entries and vector entries are read from actual memory;
all rows, counters, arithmetic, writes and cleanup are charged. -/
theorem matvec_executes {rows n : ℕ} (d : Data (rows*n) n) (l : OutputLayout) (B : ℕ)
    (hsized : d.Sized B) (hl : l.Sized B) (hm : rows*n < 2^B) (hr : rows < 2^B)
    (hW : 0 < addressValue d.width) (hsep : l.Separated rows (addressValue d.width))
    (hinsep : InputSeparated d l.positiveBase l.negativeBase rows)
    (hpfit : ∀ row, (d.outputPositive row).bits.length ≤ addressValue d.width)
    (hnfit : ∀ row, (d.outputNegative row).bits.length ≤ addressValue d.width)
    (input : List Bool) (tape : ℕ → Bool) (mi vi ri count outer : List Bool)
    (hmi : addressValue mi = 0) (hvi : addressValue vi = 0) (hri : addressValue ri = 0)
    (hcount : addressValue count = n) (houter : addressValue outer = rows)
    (hml : mi.length ≤ B) (hvl : vi.length ≤ B) (hrl : ri.length ≤ B)
    (hcl : count.length ≤ B) (hol : outer.length ≤ B)
    (positive negative : Vector (List Bool) rows) (origin : ℤ) (s : Store)
    (hready : Ready s.val (dotValues 0 0)) (hdata : Stored d s.val) (hidx : Indices s.val mi vi)
    (hout : OutputStored l (addressValue d.width) ri positive negative s.val)
    (h107 : BankArray.Word s.val 107 count) (h106 : Blank s.val 106) (h37 : Blank s.val 37)
    (h108 : s.val.tapes 108 = BitTape.shifted outer origin) :
    ∃ cost, ∃ t : Store, ∃ finalMatrixIndex finalVectorIndex finalRowIndex : List Bool,
      cost ≤ matvecCost rows n B ∧ Executes input tape matvecCode cost s t ∧
      addressValue finalMatrixIndex = rows*n ∧ addressValue finalVectorIndex = 0 ∧
      addressValue finalRowIndex = rows ∧
      finalMatrixIndex.length ≤ B ∧ finalVectorIndex.length ≤ B ∧ finalRowIndex.length ≤ B ∧
      Indices t.val finalMatrixIndex finalVectorIndex ∧ Stored d t.val ∧ Ready t.val (dotValues 0 0) ∧
      OutputStored l (addressValue d.width) finalRowIndex
        (Vector.ofFn d.positivePayload) (Vector.ofFn d.negativePayload) t.val ∧
      BankArray.Word t.val 107 count ∧ Blank t.val 106 ∧ Blank t.val 37 ∧ Blank t.val 108 ∧
      MatrixFrame s.val t.val ∧ OutputOutside l rows (addressValue d.width) s.val t.val := by
  let inv := MatvecInvariant d l positive negative count B s.val
  have stable : ∀ r a b, CountedShifted.Frame 108 a b → inv r a → inv r b :=
    matvec_invariant_stable d l positive negative count B s.val
  have bodyCorrect : ∀ r xs u, inv (r+1) u →
      u.val.tapes 108 = BitTape.shifted xs origin → addressValue xs = r →
      ∃ bodyCost t, Executes input tape rowCode bodyCost u t ∧ inv r t ∧
        t.val.tapes 108 = BitTape.shifted xs origin ∧ bodyCost ≤ rowCost n B := by
    intro r xs u hu hcounter _
    obtain ⟨hrem, midx, vidx, ridx, hmi, hvi, hri, hml, hvl, hrl,
      hidx, hdat, hwork, hout, hc, h106, h37, hfr, hmem⟩ := hu
    let i : Fin rows := ⟨rows-(r+1), by omega⟩
    obtain ⟨cost, t, fm, hcost, he, hfm, hfml, hrl', hti, htd, htr, hto, ht106, ht37, ht108, htm, htf⟩ :=
      row d l B hsized hl hm hr hW hsep hinsep i (hpfit i) (hnfit i) input tape
        midx vidx ridx count hmi hvi hri hcount hml hvl hrl hcl
        (fillPrefix positive d.positivePayload (rows-(r+1)))
        (fillPrefix negative d.negativePayload (rows-(r+1))) u hwork hdat hidx hout hc h106 h37
    have hnext : rows-r = i.val+1 := by dsimp [i]; omega
    have hnextOutput : OutputStored l (addressValue d.width) (Increment.bits ridx)
        (fillPrefix positive d.positivePayload (rows-r))
        (fillPrefix negative d.negativePayload (rows-r)) t.val := by
      rw [hnext]
      rw [← fillPrefix_step positive d.positivePayload i, ← fillPrefix_step negative d.negativePayload i]
      exact hto
    refine ⟨cost, t, he, ⟨by omega, fm, [], Increment.bits ridx,
      by simpa only [hnext] using hfm, rfl, ?_, hfml, by simp, hrl', hti, htd, htr, hnextOutput,
      ?_, ht106, ht37, hfr.trans htf, ?_⟩, ht108.trans hcounter, hcost⟩
    · rw [Increment.bits_value, hri]; dsimp [i] at hnext; omega
    · exact BankArray.word_of_eq
        (htf.2.2.2.1 107 (Or.inr (by omega)) (Or.inr (by omega))
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) hc
    · exact hmem.trans (OutputOutside.of_write i _ _ (FixedWidth.bits_length _ _) (FixedWidth.bits_length _ _) htm)
  have hinitial : inv rows s := by
    refine ⟨le_rfl, mi, vi, ri, ?_, hvi, ?_, hml, hvl, hrl, hidx, hdata, hready,
      ?_, h107, h106, h37, MatrixFrame.refl s.val, OutputOutside.refl l rows _ s.val⟩
    · simpa using hmi
    · simpa using hri
    · simpa using hout
  obtain ⟨cost, a, finalCount, he, haInv, haCount, haLen, _, haCost⟩ :=
    CountedShifted.executes 108 origin rowCode input tape inv (fun _ => rowCost n B)
      stable bodyCorrect rows outer s houter h108 hinitial
  obtain ⟨_, fm, fv, fr, hfm, hfv, hfr, hfml, hfvl, hfrl, hai, had, har, hao, ha107, ha106, ha37, haf, ham⟩ := haInv
  obtain ⟨t, et, ht, ft⟩ := WordCall.clear 108 input tape finalCount origin a haCount
  have keep (i : ℕ) (hi : i ≠ 108) : t.val.tapes i = a.val.tapes i := by simp [ht, hi]
  have frame : MatrixFrame a.val t.val :=
    ⟨ft.2.1, ft.2.2.2.1, ft.2.2.2.2.1, fun i _ _ _ _ _ _ _ h108 => keep i h108,
      fun i _ _ _ h26 h27 _ _ => ft.2.2.2.2.2.2 i h26 h27⟩
  refine ⟨cost+(6*finalCount.length+4), t, fm, fv, fr, ?_, he.seq et,
    by simpa using hfm, hfv, by simpa using hfr, hfml, hfvl, hfrl,
    ⟨BankArray.word_of_eq (keep 102 (by omega)) hai.1,
      BankArray.word_of_eq (keep 103 (by omega)) hai.2⟩,
    had.of_matrix ft.2.2.1 frame, har.of_tapes (fun i hi => keep i (by omega)), ?_,
    BankArray.word_of_eq (keep 107 (by omega)) ha107,
    RationalAccumulator.blank_of_eq (keep 106 (by omega)) ha106,
    RationalAccumulator.blank_of_eq (keep 37 (by omega)) ha37,
    ⟨origin+finalCount.length, by simp [ht]⟩,
    haf.trans frame, ham.trans (OutputOutside.of_memory ft.2.2.1)⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at haCost
    have hlen : finalCount.length ≤ B := haLen.trans_le hol
    have hcounter : (rows+1)*(13*outer.length+15) ≤ (rows+1)*(13*B+15) := by gcongr
    dsimp [matvecCost]
    omega
  · have hh := hao.of_memory ft.2.2.1 (fun i hi => keep i (by omega))
    simpa using hh

end Maxwell.Cost.CalibrationMatrix
