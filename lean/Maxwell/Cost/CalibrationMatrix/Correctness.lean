import Maxwell.Cost.CalibrationMatrix.Matvec
import Maxwell.Cost.CalibrationMatrix.Semantics

namespace Maxwell.Cost.CalibrationMatrix
open Structured
open RationalAccumulator (Blank)

theorem rowCost_le (n B : ℕ) : rowCost n B ≤ 600000*(n+1)*(B+2)^2 := by
  have hbase : 13*B+15 ≤ 20*(B+2)^2 := by nlinarith
  have hsmall : 46*B+44 ≤ 40*(B+2)^2 := by nlinarith
  calc
    _ ≤ (n+1)*(20*(B+2)^2) + n*(510000*(B+2)^2) + 80000*(B+2)^2 + 40*(B+2)^2 := by
      dsimp [rowCost, dotCost]
      nlinarith only [Nat.mul_le_mul_left (n+1) hbase, hsmall]
    _ ≤ _ := by nlinarith only [Nat.zero_le ((89980*n+519940)*(B+2)^2)]

theorem matvecCost_le (rows n B : ℕ) :
    matvecCost rows n B ≤ 610000*(rows+1)*(n+1)*(B+2)^2 := by
  have hrow := Nat.mul_le_mul_left rows (rowCost_le n B)
  have hbase : 13*B+15 ≤ 20*(B+2)^2 := by nlinarith
  have hsmall : 6*B+4 ≤ 10*(B+2)^2 := by nlinarith
  calc
    _ ≤ (rows+1)*(20*(B+2)^2) + rows*(600000*(n+1)*(B+2)^2) + 10*(B+2)^2 := by
      dsimp [matvecCost]
      nlinarith only [hrow, Nat.mul_le_mul_left (rows+1) hbase, hsmall]
    _ ≤ _ := by
      nlinarith only [Nat.zero_le ((10000*rows*n+9980*rows+610000*n+609970)*(B+2)^2)]

theorem matvec_compiled_run {rows n : ℕ} (d : Data (rows*n) n) (l : OutputLayout) (B : ℕ)
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
    ∃ t : Store, ∃ finalMatrixIndex finalVectorIndex finalRowIndex : List Bool,
      (runPriced (matvecCode.compile.next input tape) (matvecCost rows n B+1) s.val).finished =
        some (t.place matvecCode.size) ∧
      (runPriced (matvecCode.compile.next input tape) (matvecCost rows n B+1) s.val).instructions ≤
        matvecCost rows n B ∧
      addressValue finalMatrixIndex = rows*n ∧ addressValue finalVectorIndex = 0 ∧
      addressValue finalRowIndex = rows ∧
      finalMatrixIndex.length ≤ B ∧ finalVectorIndex.length ≤ B ∧ finalRowIndex.length ≤ B ∧
      Indices t.val finalMatrixIndex finalVectorIndex ∧ Stored d t.val ∧ Ready t.val (dotValues 0 0) ∧
      OutputStored l (addressValue d.width) finalRowIndex
        (Vector.ofFn d.positivePayload) (Vector.ofFn d.negativePayload) t.val ∧
      BankArray.Word t.val 107 count ∧ Blank t.val 106 ∧ Blank t.val 37 ∧ Blank t.val 108 ∧
      MatrixFrame s.val t.val ∧ OutputOutside l rows (addressValue d.width) s.val t.val := by
  obtain ⟨cost, t, fm, fv, fr, hc, he, ht⟩ := matvec_executes d l B hsized hl hm hr hW hsep hinsep
    hpfit hnfit input tape mi vi ri count outer hmi hvi hri hcount houter hml hvl hrl hcl hol
    positive negative origin s hready hdata hidx hout h107 h106 h37 h108
  have hrun := he.compiled_run (matvecCost rows n B+1) (by omega)
  exact ⟨t, fm, fv, fr, hrun.1, hrun.2 ▸ hc, ht⟩

/-- The stored output arrays are the exact unreduced positive and negative
channels used by the integer Horner and mode-power semantics. -/
theorem OutputStored.matvec_channels {n : ℕ} {d : Data (n*n) n} {A : ChannelMatrix n}
    {x : Channels n} (h : d.Decodes A x) {l : OutputLayout} {index : List Bool} {s : BitRAMState}
    (ho : OutputStored l (addressValue d.width) index
      (Vector.ofFn d.positivePayload) (Vector.ofFn d.negativePayload) s) :
    OutputStored l (addressValue d.width) index
      (channelWords (addressValue d.width) (matvec A x).positive)
      (channelWords (addressValue d.width) (matvec A x).negative) s := by
  simpa only [d.positivePayload_eq_matvec h, d.negativePayload_eq_matvec h] using ho

end Maxwell.Cost.CalibrationMatrix
