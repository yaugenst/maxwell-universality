import Maxwell.Certificate.LowCompressionWitness.SignedSound
import Maxwell.Certificate.LowCompressionWitness.UpperData
import Maxwell.Certificate.PointInertia.UpperNegative
namespace Maxwell.Certificate.LowCompressionWitness
open Matrix DyadicRectangle PointInertia
open scoped ComplexOrder
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperNegativeSelect (i : Fin 4) : Fin 28 := ⟨i.val+0,by omega⟩
noncomputable def UpperNegativeShiftCheck (i j : Fin 4) : Bool := Trigonometric.rectangleSubsetCheck
    ((shiftedEntry true (UpperCompression (UpperNegativeSelect i) (UpperNegativeSelect j)) i j).toRectangle 52) (PointInertia.UpperNegative.enclosure0 i j)
theorem UpperNegativeShiftRow0 : ∀ j : Fin 4, UpperNegativeShiftCheck 0 j = true := by decide +kernel
theorem UpperNegativeShiftRow1 : ∀ j : Fin 4, UpperNegativeShiftCheck 1 j = true := by decide +kernel
theorem UpperNegativeShiftRow2 : ∀ j : Fin 4, UpperNegativeShiftCheck 2 j = true := by decide +kernel
theorem UpperNegativeShiftRow3 : ∀ j : Fin 4, UpperNegativeShiftCheck 3 j = true := by decide +kernel
theorem UpperNegativeShiftCheck_all (i j : Fin 4) : UpperNegativeShiftCheck i j = true := by
  fin_cases i
  · exact UpperNegativeShiftRow0 j
  · exact UpperNegativeShiftRow1 j
  · exact UpperNegativeShiftRow2 j
  · exact UpperNegativeShiftRow3 j
theorem UpperNegative_selected_psd (F A : Matrix (Fin 42) (Fin 28) ℂ)
    (hc : ∀ i j, (UpperCompression i j).Contains 52 (HermitianCompression.matrix F A i j)) :
    (signedMatrix true (HermitianCompression.matrix (F.submatrix id UpperNegativeSelect) (A.submatrix id UpperNegativeSelect))).PosSemidef :=
  selected_psd_of_check F A UpperCompression UpperNegativeSelect true PointInertia.UpperNegative.enclosure0
    PointInertia.UpperNegative.proposal PointInertia.UpperNegative.accepted hc UpperNegativeShiftCheck_all
end Maxwell.Certificate.LowCompressionWitness
