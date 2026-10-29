import Maxwell.Certificate.LowCompressionWitness.SignedSound
import Maxwell.Certificate.LowCompressionWitness.LowerData
import Maxwell.Certificate.PointInertia.LowerPositive
namespace Maxwell.Certificate.LowCompressionWitness
open Matrix DyadicRectangle PointInertia
open scoped ComplexOrder
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerPositiveSelect (i : Fin 26) : Fin 28 := ⟨i.val+2,by omega⟩
noncomputable def LowerPositiveShiftCheck (i j : Fin 26) : Bool := Trigonometric.rectangleSubsetCheck
    ((shiftedEntry false (LowerCompression (LowerPositiveSelect i) (LowerPositiveSelect j)) i j).toRectangle 52) (PointInertia.LowerPositive.enclosure0 i j)
theorem LowerPositiveShiftRow0 : ∀ j : Fin 26, LowerPositiveShiftCheck 0 j = true := by decide +kernel
theorem LowerPositiveShiftRow1 : ∀ j : Fin 26, LowerPositiveShiftCheck 1 j = true := by decide +kernel
theorem LowerPositiveShiftRow2 : ∀ j : Fin 26, LowerPositiveShiftCheck 2 j = true := by decide +kernel
theorem LowerPositiveShiftRow3 : ∀ j : Fin 26, LowerPositiveShiftCheck 3 j = true := by decide +kernel
theorem LowerPositiveShiftRow4 : ∀ j : Fin 26, LowerPositiveShiftCheck 4 j = true := by decide +kernel
theorem LowerPositiveShiftRow5 : ∀ j : Fin 26, LowerPositiveShiftCheck 5 j = true := by decide +kernel
theorem LowerPositiveShiftRow6 : ∀ j : Fin 26, LowerPositiveShiftCheck 6 j = true := by decide +kernel
theorem LowerPositiveShiftRow7 : ∀ j : Fin 26, LowerPositiveShiftCheck 7 j = true := by decide +kernel
theorem LowerPositiveShiftRow8 : ∀ j : Fin 26, LowerPositiveShiftCheck 8 j = true := by decide +kernel
theorem LowerPositiveShiftRow9 : ∀ j : Fin 26, LowerPositiveShiftCheck 9 j = true := by decide +kernel
theorem LowerPositiveShiftRow10 : ∀ j : Fin 26, LowerPositiveShiftCheck 10 j = true := by decide +kernel
theorem LowerPositiveShiftRow11 : ∀ j : Fin 26, LowerPositiveShiftCheck 11 j = true := by decide +kernel
theorem LowerPositiveShiftRow12 : ∀ j : Fin 26, LowerPositiveShiftCheck 12 j = true := by decide +kernel
theorem LowerPositiveShiftRow13 : ∀ j : Fin 26, LowerPositiveShiftCheck 13 j = true := by decide +kernel
theorem LowerPositiveShiftRow14 : ∀ j : Fin 26, LowerPositiveShiftCheck 14 j = true := by decide +kernel
theorem LowerPositiveShiftRow15 : ∀ j : Fin 26, LowerPositiveShiftCheck 15 j = true := by decide +kernel
theorem LowerPositiveShiftRow16 : ∀ j : Fin 26, LowerPositiveShiftCheck 16 j = true := by decide +kernel
theorem LowerPositiveShiftRow17 : ∀ j : Fin 26, LowerPositiveShiftCheck 17 j = true := by decide +kernel
theorem LowerPositiveShiftRow18 : ∀ j : Fin 26, LowerPositiveShiftCheck 18 j = true := by decide +kernel
theorem LowerPositiveShiftRow19 : ∀ j : Fin 26, LowerPositiveShiftCheck 19 j = true := by decide +kernel
theorem LowerPositiveShiftRow20 : ∀ j : Fin 26, LowerPositiveShiftCheck 20 j = true := by decide +kernel
theorem LowerPositiveShiftRow21 : ∀ j : Fin 26, LowerPositiveShiftCheck 21 j = true := by decide +kernel
theorem LowerPositiveShiftRow22 : ∀ j : Fin 26, LowerPositiveShiftCheck 22 j = true := by decide +kernel
theorem LowerPositiveShiftRow23 : ∀ j : Fin 26, LowerPositiveShiftCheck 23 j = true := by decide +kernel
theorem LowerPositiveShiftRow24 : ∀ j : Fin 26, LowerPositiveShiftCheck 24 j = true := by decide +kernel
theorem LowerPositiveShiftRow25 : ∀ j : Fin 26, LowerPositiveShiftCheck 25 j = true := by decide +kernel
theorem LowerPositiveShiftCheck_all (i j : Fin 26) : LowerPositiveShiftCheck i j = true := by
  fin_cases i
  · exact LowerPositiveShiftRow0 j
  · exact LowerPositiveShiftRow1 j
  · exact LowerPositiveShiftRow2 j
  · exact LowerPositiveShiftRow3 j
  · exact LowerPositiveShiftRow4 j
  · exact LowerPositiveShiftRow5 j
  · exact LowerPositiveShiftRow6 j
  · exact LowerPositiveShiftRow7 j
  · exact LowerPositiveShiftRow8 j
  · exact LowerPositiveShiftRow9 j
  · exact LowerPositiveShiftRow10 j
  · exact LowerPositiveShiftRow11 j
  · exact LowerPositiveShiftRow12 j
  · exact LowerPositiveShiftRow13 j
  · exact LowerPositiveShiftRow14 j
  · exact LowerPositiveShiftRow15 j
  · exact LowerPositiveShiftRow16 j
  · exact LowerPositiveShiftRow17 j
  · exact LowerPositiveShiftRow18 j
  · exact LowerPositiveShiftRow19 j
  · exact LowerPositiveShiftRow20 j
  · exact LowerPositiveShiftRow21 j
  · exact LowerPositiveShiftRow22 j
  · exact LowerPositiveShiftRow23 j
  · exact LowerPositiveShiftRow24 j
  · exact LowerPositiveShiftRow25 j
theorem LowerPositive_selected_psd (F A : Matrix (Fin 42) (Fin 28) ℂ)
    (hc : ∀ i j, (LowerCompression i j).Contains 52 (HermitianCompression.matrix F A i j)) :
    (signedMatrix false (HermitianCompression.matrix (F.submatrix id LowerPositiveSelect) (A.submatrix id LowerPositiveSelect))).PosSemidef :=
  selected_psd_of_check F A LowerCompression LowerPositiveSelect false PointInertia.LowerPositive.enclosure0
    PointInertia.LowerPositive.proposal PointInertia.LowerPositive.accepted hc LowerPositiveShiftCheck_all
end Maxwell.Certificate.LowCompressionWitness
