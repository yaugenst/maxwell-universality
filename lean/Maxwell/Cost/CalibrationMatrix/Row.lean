import Maxwell.Cost.CalibrationMatrix.RowControl
import Maxwell.Cost.CalibrationMatrix.MatrixState

namespace Maxwell.Cost.CalibrationMatrix
open Structured
open RationalAccumulator (Blank)
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem row_bound {rows n : ℕ} (row : Fin rows) : row.val*n+n ≤ rows*n := by
  have h := Nat.mul_le_mul_right n (show row.val+1 ≤ rows by omega)
  simpa [Nat.add_mul] using h

def Data.outputPositive {rows n : ℕ} (d : Data (rows*n) n) (row : Fin rows) : ℕ :=
  ∑ j, d.rowPositive (row.val*n) (row_bound row) j

def Data.outputNegative {rows n : ℕ} (d : Data (rows*n) n) (row : Fin rows) : ℕ :=
  ∑ j, d.rowNegative (row.val*n) (row_bound row) j

def Data.positivePayload {rows n : ℕ} (d : Data (rows*n) n) (row : Fin rows) : List Bool :=
  FixedWidth.bits (addressValue d.width) (d.outputPositive row).bits

def Data.negativePayload {rows n : ℕ} (d : Data (rows*n) n) (row : Fin rows) : List Bool :=
  FixedWidth.bits (addressValue d.width) (d.outputNegative row).bits

def rowCode : Code := .seq rowSetupCode (.seq dotCode (.seq writeRowCode rowAdvanceCode))

def rowCost (n B : ℕ) : ℕ := dotCost n B B + 80000*(B+2)^2 + 40*B+40

/-- One actual row loads its inner counter, runs the indexed dot product,
writes both signed channels, and resets the cursors for the next row. -/
theorem row {rows n : ℕ} (d : Data (rows*n) n) (l : OutputLayout) (B : ℕ)
    (hsized : d.Sized B) (hl : l.Sized B) (hm : rows*n < 2^B) (hr : rows < 2^B)
    (hW : 0 < addressValue d.width)
    (hsep : l.Separated rows (addressValue d.width))
    (hinsep : InputSeparated d l.positiveBase l.negativeBase rows)
    (row : Fin rows)
    (hpfit : (d.outputPositive row).bits.length ≤ addressValue d.width)
    (hnfit : (d.outputNegative row).bits.length ≤ addressValue d.width)
    (input : List Bool) (tape : ℕ → Bool) (mi vi ri count : List Bool)
    (hmi : addressValue mi = row.val*n) (hvi : addressValue vi = 0)
    (hri : addressValue ri = row.val) (hcount : addressValue count = n)
    (hml : mi.length ≤ B) (hvl : vi.length ≤ B) (hrl : ri.length ≤ B) (hcl : count.length ≤ B)
    (positive negative : Vector (List Bool) rows) (s : Store)
    (hready : Ready s.val (dotValues 0 0)) (hdata : Stored d s.val) (hidx : Indices s.val mi vi)
    (hout : OutputStored l (addressValue d.width) ri positive negative s.val)
    (h107 : BankArray.Word s.val 107 count) (h106 : Blank s.val 106) (h37 : Blank s.val 37) :
    ∃ cost, ∃ t : Store, ∃ finalMatrixIndex : List Bool,
      cost ≤ rowCost n B ∧ Executes input tape rowCode cost s t ∧
      addressValue finalMatrixIndex = (row.val+1)*n ∧ finalMatrixIndex.length ≤ B ∧
      (Increment.bits ri).length ≤ B ∧
      Indices t.val finalMatrixIndex [] ∧ Stored d t.val ∧ Ready t.val (dotValues 0 0) ∧
      OutputStored l (addressValue d.width) (Increment.bits ri)
        (positive.set row (d.positivePayload row)) (negative.set row (d.negativePayload row)) t.val ∧
      Blank t.val 106 ∧ Blank t.val 37 ∧ t.val.tapes 108 = s.val.tapes 108 ∧
      t.val.memory = MemoryWord.writeBits
        (MemoryWord.writeBits s.val.memory
          (addressValue l.positiveBase+row.val*addressValue d.width) (d.positivePayload row))
        (addressValue l.negativeBase+row.val*addressValue d.width) (d.negativePayload row) ∧
      MatrixFrame s.val t.val := by
  obtain ⟨a, ea, ha106, keepA, fa⟩ := row_setup input tape count s h107 h106
  have had := hdata.of_loop fa
  have hao := hout.of_loop fa
  have hai : Indices a.val mi vi := ⟨BankArray.word_of_eq (keepA 102 (by omega)) hidx.1,
    BankArray.word_of_eq (keepA 103 (by omega)) hidx.2⟩
  obtain ⟨co, ha106⟩ := ha106
  obtain ⟨dcost, b, fm, fv, hdcost, eb, hfm, _, hfml, hfvl, hbi, hbd, hbr, hb106, fb⟩ :=
    dot d (row.val*n) B (row_bound row) hsized hm (hpfit.trans hsized.2.1) (hnfit.trans hsized.2.1)
      input tape mi vi count hmi hvi hml hvl hcount co a ha106
      (hready.of_tapes (fun i hi => keepA i (by omega))) had hai
  have hbo := hao.of_loop fb
  have keepB (i : ℕ) (hi : i = 37 ∨ i = 108) : b.val.tapes i = a.val.tapes i :=
    fb.2.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have hb37 := RationalAccumulator.blank_of_eq ((keepB 37 (by omega)).trans (keepA 37 (by omega))) h37
  obtain ⟨wcost, c, hwcost, ec, hcr, hc37, hcm, hcpos, hcneg, fc⟩ :=
    write_row input tape d.width ri l.positiveBase l.negativeBase d.clock positive negative row
      (d.outputPositive row) (d.outputNegative row) d.width_nonempty hri d.clock_length hW
      hpfit hnfit hsep b hbr hb37 hbd.width hbo.index hbo.positiveBase hbo.negativeBase
      hbd.clock hbo.positive hbo.negative
  have hcd : Stored d c.val := hbd.after_row_write l.positiveBase l.negativeBase row
    (d.positivePayload row) (d.negativePayload row) (FixedWidth.bits_length _ _)
    (FixedWidth.bits_length _ _) hinsep fc hcm
  have keepC (i : ℕ) (hi : 100 ≤ i) : c.val.tapes i = b.val.tapes i :=
    fc.2.2.2.1 i (Or.inr (by omega)) (by omega) (by omega) (by omega)
  obtain ⟨acost, t, hacost, et, htvi, htri, htr, htm, keepT, ft⟩ := row_advance input tape fv ri c
    (BankArray.word_of_eq (keepC 103 (by omega)) hbi.2)
    (BankArray.word_of_eq (keepC 104 (by omega)) hbo.index) hcr
  refine ⟨15*count.length+17+(dcost+(wcost+acost)), t, fm, ?_, ea.seq (eb.seq (ec.seq et)),
    by simpa [Nat.add_mul] using hfm, hfml,
    BankArray.increment_length_bound ri B hrl (by rw [hri]; omega),
    ⟨BankArray.word_of_eq ((keepT 102 (by omega) (by omega)).trans (keepC 102 (by omega))) hbi.1, htvi⟩,
    hcd.of_matrix htm ft, htr, ?_, ?_, ?_, ?_, ?_,
    (((MatrixFrame.of_loop fa).trans (MatrixFrame.of_loop fb)).trans (MatrixFrame.of_row fc)).trans ft⟩
  · have hwrite := writeRow_cost_le d.width ri l.positiveBase l.negativeBase
      (d.outputPositive row) (d.outputNegative row) B hsized.1 hrl hl.1 hl.2 hsized.2.1
    have hdot : dotCost n B count.length ≤ dotCost n B B := by
      dsimp [dotCost]; gcongr
    dsimp [rowCost]
    omega
  · exact ⟨htri,
      BankArray.word_of_eq ((keepT 114 (by omega) (by omega)).trans (keepC 114 (by omega))) hbo.positiveBase,
      BankArray.word_of_eq ((keepT 115 (by omega) (by omega)).trans (keepC 115 (by omega))) hbo.negativeBase,
      by simpa only [htm, Data.positivePayload] using hcpos,
      by simpa only [htm, Data.negativePayload] using hcneg⟩
  · exact RationalAccumulator.blank_of_eq
      ((keepT 106 (by omega) (by omega)).trans (keepC 106 (by omega))) hb106
  · exact RationalAccumulator.blank_of_eq (keepT 37 (by omega) (by omega)) hc37
  · exact (keepT 108 (by omega) (by omega)).trans ((keepC 108 (by omega)).trans
      ((keepB 108 (by omega)).trans (keepA 108 (by omega))))
  · simp only [htm, hcm, fb.1, fa.1, Data.positivePayload, Data.negativePayload]

end Maxwell.Cost.CalibrationMatrix
