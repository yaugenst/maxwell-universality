import Maxwell.Continuum.RationalDefinitenessComplex
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Literal operator semantics for the finite rational sign decision. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

def rationalOperator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (fun i j => (A i j : ℂ))

theorem rationalOperator_inner {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (z : EuclideanSpace ℂ (Fin n)) : inner ℂ z (rationalOperator A z)=complexQuadratic A z := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm]
  change (∑ i, star (z i)*(∑ j, (A i j : ℂ)*z j))=_
  unfold complexQuadratic
  simp only [Finset.mul_sum,mul_assoc]

theorem negativeTest_operator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j, A i j=A j i) :
    negativeTest A=true ↔ ∀ z : EuclideanSpace ℂ (Fin n), z≠0 →
      (inner ℂ z (rationalOperator A z)).re<0 := by
  rw [negativeTest_complex A hA]
  constructor
  · intro h z hz
    rw [rationalOperator_inner]
    apply h z
    intro he
    apply hz
    exact PiLp.ext (fun i => congrFun he i)
  · intro h z hz
    have he : (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin n))≠0 := by
      intro he
      apply hz
      exact congrArg (fun v : EuclideanSpace ℂ (Fin n) => (fun i => v i)) he
    simpa only [rationalOperator_inner] using h (WithLp.toLp 2 z) he

theorem negativeTest_operator_false {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j, A i j=A j i) (h : negativeTest A=false) :
    ∃ z : EuclideanSpace ℂ (Fin n), z≠0 ∧ 0≤(inner ℂ z (rationalOperator A z)).re := by
  have hn : ¬ ∀ z : EuclideanSpace ℂ (Fin n), z≠0 →
      (inner ℂ z (rationalOperator A z)).re<0 := by
    intro hp
    have ht := (negativeTest_operator A hA).mpr hp
    simp [h] at ht
  push Not at hn
  exact hn

theorem quadratic_operator_error {n : ℕ}
    (A B : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    {η : ℝ} (h : ‖A-B‖≤η) (z : EuclideanSpace ℂ (Fin n)) :
    |(inner ℂ z (A z)).re-(inner ℂ z (B z)).re|≤η*‖z‖^2 := by
  have hi : inner ℂ z (A z)-inner ℂ z (B z)=inner ℂ z ((A-B) z) := by
    rw [sub_apply,inner_sub_right]
  calc
    _ = |(inner ℂ z ((A-B) z)).re| := by rw [← hi,Complex.sub_re]
    _ ≤ ‖inner ℂ z ((A-B) z)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖z‖*‖(A-B) z‖ := norm_inner_le_norm _ _
    _ ≤ ‖z‖*(η*‖z‖) := mul_le_mul_of_nonneg_left ((A-B).le_of_opNorm_le h z) (norm_nonneg _)
    _ = _ := by ring

#print axioms negativeTest_operator
#print axioms quadratic_operator_error

end Maxwell.Continuum.Calibration
