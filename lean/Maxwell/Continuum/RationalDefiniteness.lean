import Maxwell.Continuum.RationalDefinitenessQuadratic
import Maxwell.Continuum.RationalFiniteWidths

/-! Executable exact definiteness tests. Singular pivots return false and
therefore never cause an undecidable sign or a division-by-zero branch. -/

namespace Maxwell.Continuum.Calibration

def positiveTest : {n : ℕ} → Matrix (Fin n) (Fin n) ℚ → Bool
  | 0, _ => true
  | _n+1, A => if 0<A 0 0 then positiveTest (scalarSchur A) else false

def negativeTest {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Bool := positiveTest (-A)

def rationalMatrixReal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (A i j : ℝ)

theorem scalarSchur_ratCast {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    scalarSchur (rationalMatrixReal A)=rationalMatrixReal (scalarSchur A) := by
  ext i j
  simp only [scalarSchur,rationalMatrixReal,Rat.cast_sub,Rat.cast_mul,Rat.cast_div]

theorem positiveTest_correct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j, A i j=A j i) : positiveTest A=true ↔ StrictQuadratic (rationalMatrixReal A) := by
  induction n with
  | zero =>
    simp only [positiveTest,true_iff]
    intro x hx
    exact (hx (funext (fun i => Fin.elim0 i))).elim
  | succ n ih =>
    have hR : ∀ i j, rationalMatrixReal A i j=rationalMatrixReal A j i := by
      intro i j
      exact congrArg (fun q : ℚ => (q : ℝ)) (hA i j)
    rw [strictQuadratic_pivot _ hR,scalarSchur_ratCast,← ih _ (scalarSchur_symmetric A hA)]
    simp only [positiveTest,rationalMatrixReal,Rat.cast_pos]
    split_ifs <;> simp_all

theorem realQuadratic_rat_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℝ) :
    realQuadratic (rationalMatrixReal (-A)) x = -realQuadratic (rationalMatrixReal A) x := by
  simp only [realQuadratic,rationalMatrixReal,Matrix.neg_apply,Rat.cast_neg,mul_neg,neg_mul,
    Finset.sum_neg_distrib]

theorem negativeTest_correct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j, A i j=A j i) :
    negativeTest A=true ↔ ∀ x : Fin n → ℝ, x≠0 → realQuadratic (rationalMatrixReal A) x<0 := by
  rw [negativeTest,positiveTest_correct _ (by intro i j; simp only [Matrix.neg_apply,hA i j])]
  simp only [StrictQuadratic,realQuadratic_rat_neg,neg_pos]

theorem negativeTest_false {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j, A i j=A j i) (h : negativeTest A=false) :
    ∃ x : Fin n → ℝ, x≠0 ∧ 0≤realQuadratic (rationalMatrixReal A) x := by
  have hn : ¬ ∀ x : Fin n → ℝ, x≠0 → realQuadratic (rationalMatrixReal A) x<0 := by
    intro hp
    have ht := (negativeTest_correct A hA).mpr hp
    simp [h] at ht
  push Not at hn
  exact hn

theorem scalarSchur_width {n W : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hA : ∀ i j, RationalWords.Width (A i j) W) (hp : A 0 0≠0) (i j : Fin n) :
    RationalWords.Width (scalarSchur A i j) (4*W+1) := by
  have h := (hA i.succ j.succ).sub
    (((hA i.succ 0).mul (hA 0 j.succ)).mul ((hA 0 0).inv hp))
  simpa only [scalarSchur,div_eq_mul_inv,show W+(W+W+W)+1=4*W+1 by omega] using h

#print axioms positiveTest_correct
#print axioms negativeTest_correct
#print axioms scalarSchur_width

end Maxwell.Continuum.Calibration
