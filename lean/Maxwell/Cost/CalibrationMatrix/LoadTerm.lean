import Maxwell.Cost.CalibrationMatrix.Data
import Maxwell.Cost.CalibrationMatrix.Term

namespace Maxwell.Cost.CalibrationMatrix

open Structured

def loadTermCode : Code :=
  .seq (BankArray.readCanonicalCode 100 102 110 101 32)
    (.seq (BankArray.readCanonicalCode 100 102 111 101 33)
      (.seq (BankArray.readCanonicalCode 100 103 112 101 34)
        (BankArray.readCanonicalCode 100 103 113 101 35)))

def Data.readCap {m n : ℕ} (d : Data m n) (mi vi : List Bool) : ℕ :=
  BankArray.costCap d.width mi d.matrixPositiveBase d.clock +
  BankArray.costCap d.width mi d.matrixNegativeBase d.clock +
  BankArray.costCap d.width vi d.vectorPositiveBase d.clock +
  BankArray.costCap d.width vi d.vectorNegativeBase d.clock + 128*addressValue d.width+140

theorem load_term {m n : ℕ} (d : Data m n) (input : List Bool) (tape : ℕ → Bool)
    (mi vi : List Bool) (i : Fin m) (j : Fin n)
    (hmi : addressValue mi = i.val) (hvi : addressValue vi = j.val)
    (positive negative : ℕ) (s : Store) (hready : Ready s.val (dotValues positive negative))
    (hdata : Stored d s.val) (hindices : Indices s.val mi vi) :
    ∃ cost, ∃ t : Store, cost ≤ d.readCap mi vi ∧ Executes input tape loadTermCode cost s t ∧
      Ready t.val (termValues positive negative
        (addressValue (d.matrixPositive.get i)) (addressValue (d.matrixNegative.get i))
        (addressValue (d.vectorPositive.get j)) (addressValue (d.vectorNegative.get j))) ∧
      StepFrame s.val t.val := by
  let v1 := Function.update (dotValues positive negative) 32 (addressValue (d.matrixPositive.get i))
  let v2 := Function.update v1 33 (addressValue (d.matrixNegative.get i))
  let v3 := Function.update v2 34 (addressValue (d.vectorPositive.get j))
  obtain ⟨c1, a, hc1, ha, har, haf⟩ := read_operand 100 102 110 101 32
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    input tape d.width mi d.matrixPositiveBase d.clock d.matrixPositive i
    d.width_nonempty hmi d.clock_length s (dotValues positive negative) hready
    (by simp [dotValues]) hdata.width hindices.1 hdata.matrixPositiveBase hdata.clock hdata.matrixPositive
  have had := hdata.of_frame haf
  have hai := hindices.of_frame haf
  obtain ⟨c2, b, hc2, hb, hbr, hbf⟩ := read_operand 100 102 111 101 33
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    input tape d.width mi d.matrixNegativeBase d.clock d.matrixNegative i
    d.width_nonempty hmi d.clock_length a v1 har (by simp [v1, dotValues])
    had.width hai.1 had.matrixNegativeBase had.clock had.matrixNegative
  have hbd := had.of_frame hbf
  have hbi := hai.of_frame hbf
  obtain ⟨c3, c, hc3, hc, hcr, hcf⟩ := read_operand 100 103 112 101 34
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    input tape d.width vi d.vectorPositiveBase d.clock d.vectorPositive j
    d.width_nonempty hvi d.clock_length b v2 hbr (by simp [v2, v1, dotValues])
    hbd.width hbi.2 hbd.vectorPositiveBase hbd.clock hbd.vectorPositive
  have hcd := hbd.of_frame hcf
  have hci := hbi.of_frame hcf
  obtain ⟨c4, t, hc4, ht, htr, htf⟩ := read_operand 100 103 113 101 35
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    input tape d.width vi d.vectorNegativeBase d.clock d.vectorNegative j
    d.width_nonempty hvi d.clock_length c v3 hcr (by simp [v3, v2, v1, dotValues])
    hcd.width hci.2 hcd.vectorNegativeBase hcd.clock hcd.vectorNegative
  exact ⟨c1+(c2+(c3+c4)), t, by dsimp [Data.readCap]; omega,
    ha.seq (hb.seq (hc.seq ht)), htr, ((haf.trans hbf).trans hcf).trans htf⟩

end Maxwell.Cost.CalibrationMatrix
