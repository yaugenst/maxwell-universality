import Maxwell.Certificate.HermitianCompression
import Maxwell.Certificate.IntervalMatrixPosDef

noncomputable section
namespace Maxwell.Certificate.LowCompressionWitness
open Matrix DyadicRectangle
open scoped ComplexOrder

abbrev P0 : ℝ := 1-1/1024

def shiftedEntry {n : ℕ} (negative : Bool) (c : DyadicRectangle) (i j : Fin n) : DyadicRectangle :=
  (if negative then c.neg else c).add
    ⟨if i=j then -(4503599627370496-4398046511104) else 0, 0, 0⟩

def signedMatrix {n : ℕ} (negative : Bool) (H : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := (if negative then -H else H) - (P0:ℂ) • 1

theorem shiftedEntry_contains {n : ℕ} (negative : Bool) {c : DyadicRectangle} {z : ℂ}
    (h : c.Contains 52 z) (i j : Fin n) :
    (shiftedEntry negative c i j).Contains 52
      ((if negative then -z else z) - (P0:ℂ)*(if i=j then 1 else 0)) := by
  have hshift : (⟨if i=j then -(4503599627370496-4398046511104) else 0, 0, 0⟩ : DyadicRectangle).Contains 52
      (-((P0:ℂ)*(if i=j then 1 else 0))) := by
    by_cases he : i=j <;> norm_num [Contains, P0, he]
  have hz : (if negative then c.neg else c).Contains 52 (if negative then -z else z) := by
    cases negative
    · exact h
    · exact neg_contains h
  simpa only [shiftedEntry, sub_eq_add_neg] using add_contains hz hshift

theorem signedMatrix_isHermitian {n : ℕ} (negative : Bool)
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) :
    (signedMatrix negative H).IsHermitian := by
  have hs : ((P0:ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian :=
    Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])
  cases negative
  · exact hH.sub hs
  · exact hH.neg.sub hs

theorem matrix_select {m n k : ℕ} (F A : Matrix (Fin m) (Fin n) ℂ) (sel : Fin k → Fin n) :
    HermitianCompression.matrix (F.submatrix id sel) (A.submatrix id sel) =
      (HermitianCompression.matrix F A).submatrix sel sel := by
  ext i j
  simp [HermitianCompression.matrix, Matrix.mul_apply, Matrix.submatrix]

theorem selected_psd_of_check {m n k : ℕ}
    (F A : Matrix (Fin m) (Fin n) ℂ) (c : Matrix (Fin n) (Fin n) DyadicRectangle)
    (sel : Fin k → Fin n) (negative : Bool)
    (target : IntervalMatrix.Enclosure k) (w : IntervalMatrix.Proposal k)
    (hw : IntervalMatrix.accepts target w = true)
    (hc : ∀ i j, (c i j).Contains 52 (HermitianCompression.matrix F A i j))
    (hcheck : ∀ i j, Trigonometric.rectangleSubsetCheck
      ((shiftedEntry negative (c (sel i) (sel j)) i j).toRectangle 52) (target i j) = true) :
    (signedMatrix negative
      (HermitianCompression.matrix (F.submatrix id sel) (A.submatrix id sel))).PosSemidef := by
  apply IntervalMatrix.accepts_sound w hw
  · exact signedMatrix_isHermitian negative (HermitianCompression.isHermitian _ _)
  · intro i j
    apply Trigonometric.rectangleSubsetCheck_sound (hcheck i j)
    apply (contains_iff 52 _ _).mp
    have h := shiftedEntry_contains negative (hc (sel i) (sel j)) i j
    rw [matrix_select]
    cases negative <;> simpa [signedMatrix, Matrix.submatrix, Matrix.one_apply, smul_eq_mul] using h

theorem signed_form_bound {m n : ℕ} (F A : Matrix (Fin m) (Fin n) ℂ)
    (negative : Bool) (h : (signedMatrix negative (HermitianCompression.matrix F A)).PosSemidef)
    (p : EuclideanSpace ℂ (Fin n)) :
    P0*‖p‖^2 ≤ (if negative then -1 else 1:ℝ) *
      (inner ℂ (F.toEuclideanLin p) (A.toEuclideanLin p)).re := by
  apply HermitianCompression.signed_lower F A _ P0 _ p
  cases negative <;> simpa [signedMatrix] using h

end Maxwell.Certificate.LowCompressionWitness
