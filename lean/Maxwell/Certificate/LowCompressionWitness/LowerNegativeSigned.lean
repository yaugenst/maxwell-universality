import Maxwell.Certificate.LowCompressionWitness.SignedSound
import Maxwell.Certificate.LowCompressionWitness.LowerData
import Maxwell.Certificate.PointInertia.LowerNegative
namespace Maxwell.Certificate.LowCompressionWitness
open Matrix DyadicRectangle PointInertia
open scoped ComplexOrder
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerNegativeSelect (i : Fin 2) : Fin 28 := ⟨i.val+0,by omega⟩
noncomputable def LowerNegativeShiftCheck (i j : Fin 2) : Bool := Trigonometric.rectangleSubsetCheck
    ((shiftedEntry true (LowerCompression (LowerNegativeSelect i) (LowerNegativeSelect j)) i j).toRectangle 52) (PointInertia.LowerNegative.enclosure0 i j)
theorem LowerNegativeShiftRow0 : ∀ j : Fin 2, LowerNegativeShiftCheck 0 j = true := by decide +kernel
theorem LowerNegativeShiftRow1 : ∀ j : Fin 2, LowerNegativeShiftCheck 1 j = true := by decide +kernel
theorem LowerNegativeShiftCheck_all (i j : Fin 2) : LowerNegativeShiftCheck i j = true := by
  fin_cases i
  · exact LowerNegativeShiftRow0 j
  · exact LowerNegativeShiftRow1 j
theorem LowerNegative_selected_psd (F A : Matrix (Fin 42) (Fin 28) ℂ)
    (hc : ∀ i j, (LowerCompression i j).Contains 52 (HermitianCompression.matrix F A i j)) :
    (signedMatrix true (HermitianCompression.matrix (F.submatrix id LowerNegativeSelect) (A.submatrix id LowerNegativeSelect))).PosSemidef :=
  selected_psd_of_check F A LowerCompression LowerNegativeSelect true PointInertia.LowerNegative.enclosure0
    PointInertia.LowerNegative.proposal PointInertia.LowerNegative.accepted hc LowerNegativeShiftCheck_all
end Maxwell.Certificate.LowCompressionWitness
