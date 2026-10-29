import Maxwell.Certificate.DyadicKernelGram
import Maxwell.Certificate.DyadicKernelSchurEvalSound
import Maxwell.Certificate.DyadicKernelVectorSound
import Maxwell.Certificate.ComplexNormCertificate

namespace Maxwell.Certificate.DyadicKernel
open Matrix
open scoped ComplexOrder

def RectangularContains {m n : ℕ} (p : ℕ) (a : Rectangular m n)
    (A : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  ∀ i j, (a.entry i j).toDyadic.Contains p (A i j)

theorem dotRound_scaled_fin_contains {p q r n : ℕ} {a b : Fin n → Rectangle}
    {z w : Fin n → ℂ}
    (ha : ∀ i, (a i).toDyadic.Contains p (z i))
    (hb : ∀ i, (b i).toDyadic.Contains q (w i)) :
    (dotRound (q+r) (List.ofFn fun i => (a i,b i))).toDyadic.Contains p
      ((∑ i, z i*w i)/(2:ℂ)^r) :=
  DyadicRectangle.scaledDotCheck_sound (FFT.dotRound_checked p (q+r) a b) ha hb

theorem gramRows_contains {p r m n : ℕ} {a : Rectangular m n}
    {A : Matrix (Fin m) (Fin n) ℂ} (ha : RectangularContains p a A) :
    MatrixContains p (gramRows p r a).enclosure
      (((2:ℝ)^r)⁻¹ • (A.conjTranspose*A)) := by
  intro i j
  simp only [gramRows,Rows.enclosure_ofEnclosure]
  have hh := dotRound_scaled_fin_contains (r := r)
    (fun k => (show (conjugate (a.entry k i)).toDyadic.Contains p (star (A k i)) from by
      rw [toDyadic_conjugate]
      exact DyadicRectangle.conjugate_contains (ha k i))) (fun k => ha k j)
  convert hh using 1
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_ofNat,
    div_eq_mul_inv, mul_comm]

theorem crossRows_contains {p r m n : ℕ} {a b : Rectangular m n}
    {A B : Matrix (Fin m) (Fin n) ℂ}
    (ha : RectangularContains p a A) (hb : RectangularContains p b B) :
    MatrixContains p (crossRows p r a b).enclosure
      (((2:ℝ)^r)⁻¹ • (A.conjTranspose*B)) := by
  intro i j
  simp only [crossRows,Rows.enclosure_ofEnclosure]
  have hh := dotRound_scaled_fin_contains (r := r)
    (fun k => (show (conjugate (a.entry k i)).toDyadic.Contains p (star (A k i)) from by
      rw [toDyadic_conjugate]
      exact DyadicRectangle.conjugate_contains (ha k i))) (fun k => hb k j)
  convert hh using 1
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_ofNat,
    div_eq_mul_inv, mul_comm]

theorem hermitianPartRows_contains {p n : ℕ} {a : Rows n}
    {A : Matrix (Fin n) (Fin n) ℂ} (ha : MatrixContains p a.enclosure A) :
    MatrixContains p (hermitianPartRows a).enclosure
      ((1/2:ℂ) • (A+A.conjTranspose)) := by
  intro i j
  simp only [hermitianPartRows,Rows.enclosure_ofEnclosure]
  have hc : (conjugate (a.enclosure j i)).toDyadic.Contains p (star (A j i)) := by
    rw [toDyadic_conjugate]
    exact DyadicRectangle.conjugate_contains (ha j i)
  have hh := DyadicRectangle.contains_div_pow (r := 1)
    (DyadicRectangle.add_contains (ha i j) hc)
  rw [← toDyadic_add] at hh
  have hr := round_contains hh
  convert hr using 1
  simp only [Matrix.smul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
    smul_eq_mul,pow_one,div_eq_mul_inv,one_mul,mul_comm]

theorem diagonalShift_contains {p n : ℕ} (subtract : Bool) {bound : Rectangle}
    {a : Rows n} {C : ℝ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hb : bound.toDyadic.Contains p (C:ℂ)) (ha : MatrixContains p a.enclosure A) :
    MatrixContains p (diagonalShift subtract bound a).enclosure
      ((C:ℂ) • (1:Matrix (Fin n) (Fin n) ℂ) + if subtract then -A else A) := by
  intro i j
  have hd : (if i=j then bound else zero).toDyadic.Contains p
      (((C:ℂ) • (1:Matrix (Fin n) (Fin n) ℂ)) i j) := by
    by_cases hij : i=j
    · subst j
      simpa only [ite_true, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using hb
    · simpa only [hij, ite_false, Matrix.smul_apply, Matrix.one_apply_ne hij,
        smul_eq_mul, mul_zero] using (show zero.toDyadic.Contains p 0 from DyadicRectangle.zero_contains p)
  simp only [diagonalShift,Rows.enclosure_ofEnclosure,toDyadic_add,Matrix.add_apply]
  apply DyadicRectangle.add_contains hd
  cases subtract
  · exact ha i j
  · change (neg (a.enclosure i j)).toDyadic.Contains p (-A i j)
    rw [toDyadic_neg]
    exact DyadicRectangle.neg_contains (ha i j)

theorem gramNormEval_sound {p r m n : ℕ} {boundSquared : Rectangle}
    {a : Rectangular m n} {A : Matrix (Fin m) (Fin n) ℂ} {C : ℝ}
    (h : gramNormEval p r boundSquared a = true) (hC : 0 ≤ C)
    (hb : boundSquared.toDyadic.Contains p (((2:ℝ)^r)⁻¹*C^2:ℝ))
    (ha : RectangularContains p a A) :
    ‖ComplexNormCertificate.rectangularOperator A‖ ≤ C := by
  have hh := diagonalShift_contains true hb (gramRows_contains (r := r) ha)
  have hHerm : (((((2:ℝ)^r)⁻¹*C^2:ℝ):ℂ) • (1:Matrix (Fin n) (Fin n) ℂ) -
      ((2:ℝ)^r)⁻¹ • (A.conjTranspose*A)).IsHermitian := by
    exact (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])).sub
      ((Matrix.isHermitian_conjTranspose_mul_self A).smul (by simp [IsSelfAdjoint]))
  have hp := schurEvalRows_posDef h hHerm (by simpa only [Bool.true_eq, ite_true, sub_eq_add_neg] using hh)
  exact ComplexNormCertificate.rectangular_norm_le_of_scaled_difference A C ((2:ℝ)^r)⁻¹
    hC (by positivity) hp.posSemidef

theorem hermitianNormEval_sound {p n : ℕ} {bound : Rectangle} {a : Rows n}
    {H : Matrix (Fin n) (Fin n) ℂ} {C : ℝ}
    (h : hermitianNormEval p bound a = true) (hH : H.IsHermitian) (hC : 0 ≤ C)
    (hb : bound.toDyadic.Contains p (C:ℂ)) (ha : MatrixContains p a.enclosure H) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) H‖ ≤ C := by
  have hc : ((C:ℂ) • (1:Matrix (Fin n) (Fin n) ℂ)).IsHermitian :=
    Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])
  have hs := Bool.and_eq_true_iff.mp h
  apply ComplexNormCertificate.hermitian_norm_le H hH C hC
  · apply (schurEvalRows_posDef hs.1 (hc.add hH) ?_).posSemidef
    simpa only [Bool.false_eq_true, ite_false] using diagonalShift_contains false hb ha
  · apply (schurEvalRows_posDef hs.2 (hc.sub hH) ?_).posSemidef
    simpa only [Bool.true_eq, ite_true, sub_eq_add_neg] using diagonalShift_contains true hb ha

end Maxwell.Certificate.DyadicKernel
