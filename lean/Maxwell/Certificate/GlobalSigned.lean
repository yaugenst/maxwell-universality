import Maxwell.Certificate.DyadicKernelSigned
import Maxwell.Certificate.DyadicKernelSchurSound
import Maxwell.Certificate.LowCompressionWitness.SignedSound

namespace Maxwell.Certificate.GlobalSigned
open Matrix DyadicKernel
open scoped ComplexOrder

theorem signedEntry_toDyadic {n : ℕ} (negative : Bool) (a : Rectangle) (i j : Fin n) :
    (signedEntry negative a i j).toDyadic =
      LowCompressionWitness.shiftedEntry negative a.toDyadic i j := by
  cases negative <;> cases a <;> rfl

theorem selected_posDef {m n k : ℕ}
    (F A : Matrix (Fin m) (Fin n) ℂ) (c : DyadicKernel.Enclosure n)
    (sel : Fin k → Fin n) (negative : Bool)
    (target : DyadicKernel.Enclosure k) (w : SchurProposal k)
    (hw : schurAccepts 52 target w = true)
    (hc : ∀ i j, (c i j).toDyadic.Contains 52 (HermitianCompression.matrix F A i j))
    (hcheck : ∀ i j, j ≤ i → subsetCheck (signedEntry negative (c (sel i) (sel j)) i j)
      (target i j) = true)
    (hupper : ∀ i j, i < j → target i j = conjugate (target j i)) :
    (LowCompressionWitness.signedMatrix negative
      (HermitianCompression.matrix (F.submatrix id sel) (A.submatrix id sel))).PosDef := by
  have hH := LowCompressionWitness.signedMatrix_isHermitian negative
      (HermitianCompression.isHermitian (F.submatrix id sel) (A.submatrix id sel))
  have hlower (i j : Fin k) (hji : j ≤ i) :
      (target i j).toDyadic.Contains 52
        (LowCompressionWitness.signedMatrix negative
          (HermitianCompression.matrix (F.submatrix id sel) (A.submatrix id sel)) i j) := by
    have hh := hcheck i j hji
    rw [subsetCheck_eq, signedEntry_toDyadic] at hh
    apply DyadicRectangle.subsetCheck_sound hh
    have hz := LowCompressionWitness.shiftedEntry_contains negative (hc (sel i) (sel j)) i j
    rw [LowCompressionWitness.matrix_select]
    cases negative <;>
      simpa [LowCompressionWitness.signedMatrix, Matrix.submatrix, Matrix.one_apply, smul_eq_mul]
        using hz
  apply schurAccepts_posDef w hw hH
  intro i j
  by_cases hji : j ≤ i
  · exact hlower i j hji
  · rw [hupper i j (lt_of_not_ge hji), toDyadic_conjugate]
    rw [← hH.apply i j]
    exact DyadicRectangle.conjugate_contains (hlower j i (le_of_lt (lt_of_not_ge hji)))

end Maxwell.Certificate.GlobalSigned
