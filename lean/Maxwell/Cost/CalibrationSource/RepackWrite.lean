import Maxwell.Cost.CalibrationMatrix.Affine.Write
import Maxwell.Cost.CalibrationMatrix.Rows

/-! Repack the shared qhat coefficients into the calibration word width.
The source and destination widths may differ; the read stage supplies the
exact canonical words and this stage performs actual indexed writes. -/
namespace Maxwell.Cost.CalibrationSource.Repack
open Structured CalibrationMatrix
open RationalAccumulator (Blank)
set_option maxHeartbeats 1000000

def writeCode : Code := .seq (Affine.writePairCode 161 162) clearDotCode

/-- Two canonical coefficient channels are padded to the calibration width,
written to the sparse-record arrays, and their temporary words reclaimed. -/
theorem write {m : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (width index positiveBase negativeBase clock : List Bool)
    (positiveWords negativeWords : Vector (List Bool) m) (row : Fin m) (positive negative : ℕ)
    (hwidth : 0 < width.length) (hindex : addressValue index = row.val)
    (hclock : clock.length = addressValue width) (hpositive : 0 < addressValue width)
    (hpfit : positive.bits.length ≤ addressValue width) (hnfit : negative.bits.length ≤ addressValue width)
    (hsep : IncidenceEncoding.Separated (addressValue positiveBase) (m*addressValue width)
      (addressValue negativeBase) (m*addressValue width))
    (s : Store) (hready : Ready s.val (dotValues positive negative)) (h37 : Blank s.val 37)
    (h100 : BankArray.Word s.val 100 width) (h104 : BankArray.Word s.val 104 index)
    (h161 : BankArray.Word s.val 161 positiveBase) (h162 : BankArray.Word s.val 162 negativeBase)
    (h101 : BankArray.Word s.val 101 clock)
    (hpa : BitArray.Represents s.val.memory (addressValue positiveBase) (addressValue width) positiveWords)
    (hna : BitArray.Represents s.val.memory (addressValue negativeBase) (addressValue width) negativeWords) :
    ∃ cost t, cost ≤
        BankArray.costCap width index positiveBase (FixedWidth.bits (addressValue width) positive.bits)+
        BankArray.costCap width index negativeBase (FixedWidth.bits (addressValue width) negative.bits)+
        240*addressValue width+240 ∧
      Executes input tape writeCode cost s t ∧ Ready t.val (dotValues 0 0) ∧ Blank t.val 37 ∧
      t.val.memory = MemoryWord.writeBits
        (MemoryWord.writeBits s.val.memory (addressValue positiveBase+row.val*addressValue width)
          (FixedWidth.bits (addressValue width) positive.bits))
        (addressValue negativeBase+row.val*addressValue width) (FixedWidth.bits (addressValue width) negative.bits) ∧
      BitArray.Represents t.val.memory (addressValue positiveBase) (addressValue width)
        (positiveWords.set row (FixedWidth.bits (addressValue width) positive.bits)) ∧
      BitArray.Represents t.val.memory (addressValue negativeBase) (addressValue width)
        (negativeWords.set row (FixedWidth.bits (addressValue width) negative.bits)) ∧ RowFrame s.val t.val := by
  obtain ⟨wc,a,hw,ew,ar,a37,am,ap,an,af⟩ := Affine.write_pair 161 162
    (by omega) (by omega) input tape width index positiveBase negativeBase clock positiveWords negativeWords
      row positive negative hwidth hindex hclock hpositive hpfit hnfit hsep s hready h37
      h100 h104 h161 h162 h101 hpa hna
  obtain ⟨t,et,tr,t37,tm,tf⟩ := clear_dot input tape positive negative a ar a37
  exact ⟨wc+(6*(positive.bits.length+negative.bits.length)+8),t,by omega,ew.seq et,tr,t37,
    tm.trans am,by simpa only [tm] using ap,by simpa only [tm] using an,af.trans tf⟩

/-- The scalar per-row write cost has the same polynomial width bound as
the existing finite inverse's signed channel writer. -/
theorem write_cost_bound (width index positiveBase negativeBase : List Bool)
    (positive negative B : ℕ) (hw : width.length ≤ B) (hi : index.length ≤ B)
    (hp : positiveBase.length ≤ B) (hn : negativeBase.length ≤ B)
    (hW : addressValue width ≤ B) :
    BankArray.costCap width index positiveBase (FixedWidth.bits (addressValue width) positive.bits)+
      BankArray.costCap width index negativeBase (FixedWidth.bits (addressValue width) negative.bits)+
      240*addressValue width+240 ≤ 81000*(B+2)^2 := by
  have h := writeRow_cost_le width index positiveBase negativeBase positive negative B hw hi hp hn hW
  nlinarith

end Maxwell.Cost.CalibrationSource.Repack
