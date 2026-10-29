import Maxwell.Certificate.GlobalComputedCompression
import Maxwell.Certificate.DyadicKernelGramSound
import Maxwell.Certificate.LowCompressionWitness.SignedSound

namespace Maxwell.Certificate.DyadicKernel
open Matrix
open scoped ComplexOrder

theorem compressionRows_contains {m n : ℕ} {field action : Rectangular m n}
    {F A : Matrix (Fin m) (Fin n) ℂ}
    (hf : RectangularContains 52 field F) (ha : RectangularContains 52 action A) :
    MatrixContains 52 (compressionRows field action).enclosure (HermitianCompression.matrix F A) := by
  simpa only [compressionRows,pow_zero,inv_one,one_smul,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,HermitianCompression.matrix] using
      hermitianPartRows_contains (crossRows_contains (r := 0) hf ha)

theorem signedCompressionRows_contains {m n : ℕ} {field action : Rectangular m n}
    {F A : Matrix (Fin m) (Fin n) ℂ} (negative : Bool)
    (hf : RectangularContains 52 field F) (ha : RectangularContains 52 action A) :
    MatrixContains 52 (signedCompressionRows negative field action).enclosure
      (LowCompressionWitness.signedMatrix negative (HermitianCompression.matrix F A)) := by
  intro i j
  have hc := compressionRows_contains hf ha i j
  have hs := LowCompressionWitness.shiftedEntry_contains negative hc i j
  have he (a : Rectangle) : (signedEntry negative a i j).toDyadic =
      LowCompressionWitness.shiftedEntry negative a.toDyadic i j := by
    cases negative <;> cases a <;> rfl
  rw [signedCompressionRows,Rows.enclosure_ofEnclosure,he]
  cases negative <;>
    simpa only [LowCompressionWitness.signedMatrix,Matrix.sub_apply,Matrix.neg_apply,
      Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,Bool.false_eq_true,Bool.true_eq,
      ite_true,ite_false] using hs

theorem compressionEval_posDef {m n : ℕ} {field action : Rectangular m n}
    {F A : Matrix (Fin m) (Fin n) ℂ} {negative : Bool}
    (h : compressionEval negative field action = true)
    (hf : RectangularContains 52 field F) (ha : RectangularContains 52 action A) :
    (LowCompressionWitness.signedMatrix negative (HermitianCompression.matrix F A)).PosDef :=
  schurEvalRows_posDef h
    (LowCompressionWitness.signedMatrix_isHermitian negative (HermitianCompression.isHermitian F A))
    (signedCompressionRows_contains negative hf ha)

theorem compressionEval_form {m n : ℕ} {field action : Rectangular m n}
    {F A : Matrix (Fin m) (Fin n) ℂ} {negative : Bool}
    (h : compressionEval negative field action = true)
    (hf : RectangularContains 52 field F) (ha : RectangularContains 52 action A)
    (x : EuclideanSpace ℂ (Fin n)) :
    (1-1/1024:ℝ)*‖x‖^2 ≤ (if negative then -1 else 1:ℝ)*
      (inner ℂ (F.toEuclideanLin x) (A.toEuclideanLin x)).re :=
  LowCompressionWitness.signed_form_bound F A negative (compressionEval_posDef h hf ha).posSemidef x

end Maxwell.Certificate.DyadicKernel
