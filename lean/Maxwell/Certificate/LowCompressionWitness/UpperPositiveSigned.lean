import Maxwell.Certificate.LowCompressionWitness.SignedSound
import Maxwell.Certificate.LowCompressionWitness.UpperData
import Maxwell.Certificate.PointInertia.UpperPositive
namespace Maxwell.Certificate.LowCompressionWitness
open Matrix DyadicRectangle PointInertia
open scoped ComplexOrder
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperPositiveSelect (i : Fin 24) : Fin 28 := ⟨i.val+4,by omega⟩
noncomputable def UpperPositiveShiftCheck (i j : Fin 24) : Bool := Trigonometric.rectangleSubsetCheck
    ((shiftedEntry false (UpperCompression (UpperPositiveSelect i) (UpperPositiveSelect j)) i j).toRectangle 52) (PointInertia.UpperPositive.enclosure0 i j)
theorem UpperPositiveShiftRow0 : ∀ j : Fin 24, UpperPositiveShiftCheck 0 j = true := by decide +kernel
theorem UpperPositiveShiftRow1 : ∀ j : Fin 24, UpperPositiveShiftCheck 1 j = true := by decide +kernel
theorem UpperPositiveShiftRow2 : ∀ j : Fin 24, UpperPositiveShiftCheck 2 j = true := by decide +kernel
theorem UpperPositiveShiftRow3 : ∀ j : Fin 24, UpperPositiveShiftCheck 3 j = true := by decide +kernel
theorem UpperPositiveShiftRow4 : ∀ j : Fin 24, UpperPositiveShiftCheck 4 j = true := by decide +kernel
theorem UpperPositiveShiftRow5 : ∀ j : Fin 24, UpperPositiveShiftCheck 5 j = true := by decide +kernel
theorem UpperPositiveShiftRow6 : ∀ j : Fin 24, UpperPositiveShiftCheck 6 j = true := by decide +kernel
theorem UpperPositiveShiftRow7 : ∀ j : Fin 24, UpperPositiveShiftCheck 7 j = true := by decide +kernel
theorem UpperPositiveShiftRow8 : ∀ j : Fin 24, UpperPositiveShiftCheck 8 j = true := by decide +kernel
theorem UpperPositiveShiftRow9 : ∀ j : Fin 24, UpperPositiveShiftCheck 9 j = true := by decide +kernel
theorem UpperPositiveShiftRow10 : ∀ j : Fin 24, UpperPositiveShiftCheck 10 j = true := by decide +kernel
theorem UpperPositiveShiftRow11 : ∀ j : Fin 24, UpperPositiveShiftCheck 11 j = true := by decide +kernel
theorem UpperPositiveShiftRow12 : ∀ j : Fin 24, UpperPositiveShiftCheck 12 j = true := by decide +kernel
theorem UpperPositiveShiftRow13 : ∀ j : Fin 24, UpperPositiveShiftCheck 13 j = true := by decide +kernel
theorem UpperPositiveShiftRow14 : ∀ j : Fin 24, UpperPositiveShiftCheck 14 j = true := by decide +kernel
theorem UpperPositiveShiftRow15 : ∀ j : Fin 24, UpperPositiveShiftCheck 15 j = true := by decide +kernel
theorem UpperPositiveShiftRow16 : ∀ j : Fin 24, UpperPositiveShiftCheck 16 j = true := by decide +kernel
theorem UpperPositiveShiftRow17 : ∀ j : Fin 24, UpperPositiveShiftCheck 17 j = true := by decide +kernel
theorem UpperPositiveShiftRow18 : ∀ j : Fin 24, UpperPositiveShiftCheck 18 j = true := by decide +kernel
theorem UpperPositiveShiftRow19 : ∀ j : Fin 24, UpperPositiveShiftCheck 19 j = true := by decide +kernel
theorem UpperPositiveShiftRow20 : ∀ j : Fin 24, UpperPositiveShiftCheck 20 j = true := by decide +kernel
theorem UpperPositiveShiftRow21 : ∀ j : Fin 24, UpperPositiveShiftCheck 21 j = true := by decide +kernel
theorem UpperPositiveShiftRow22 : ∀ j : Fin 24, UpperPositiveShiftCheck 22 j = true := by decide +kernel
theorem UpperPositiveShiftRow23 : ∀ j : Fin 24, UpperPositiveShiftCheck 23 j = true := by decide +kernel
theorem UpperPositiveShiftCheck_all (i j : Fin 24) : UpperPositiveShiftCheck i j = true := by
  fin_cases i
  · exact UpperPositiveShiftRow0 j
  · exact UpperPositiveShiftRow1 j
  · exact UpperPositiveShiftRow2 j
  · exact UpperPositiveShiftRow3 j
  · exact UpperPositiveShiftRow4 j
  · exact UpperPositiveShiftRow5 j
  · exact UpperPositiveShiftRow6 j
  · exact UpperPositiveShiftRow7 j
  · exact UpperPositiveShiftRow8 j
  · exact UpperPositiveShiftRow9 j
  · exact UpperPositiveShiftRow10 j
  · exact UpperPositiveShiftRow11 j
  · exact UpperPositiveShiftRow12 j
  · exact UpperPositiveShiftRow13 j
  · exact UpperPositiveShiftRow14 j
  · exact UpperPositiveShiftRow15 j
  · exact UpperPositiveShiftRow16 j
  · exact UpperPositiveShiftRow17 j
  · exact UpperPositiveShiftRow18 j
  · exact UpperPositiveShiftRow19 j
  · exact UpperPositiveShiftRow20 j
  · exact UpperPositiveShiftRow21 j
  · exact UpperPositiveShiftRow22 j
  · exact UpperPositiveShiftRow23 j
theorem UpperPositive_selected_psd (F A : Matrix (Fin 42) (Fin 28) ℂ)
    (hc : ∀ i j, (UpperCompression i j).Contains 52 (HermitianCompression.matrix F A i j)) :
    (signedMatrix false (HermitianCompression.matrix (F.submatrix id UpperPositiveSelect) (A.submatrix id UpperPositiveSelect))).PosSemidef :=
  selected_psd_of_check F A UpperCompression UpperPositiveSelect false PointInertia.UpperPositive.enclosure0
    PointInertia.UpperPositive.proposal PointInertia.UpperPositive.accepted hc UpperPositiveShiftCheck_all
end Maxwell.Certificate.LowCompressionWitness
