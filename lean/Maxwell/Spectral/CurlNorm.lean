import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

namespace Maxwell.Spectral

open scoped BigOperators

section Operators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Double commutation is the property of the actual periodic directional
shifts; individual differences need not be self-adjoint. -/
theorem commuting_adjoint_inner (A B : E →L[ℂ] E)
    (h : A.comp B.adjoint = B.adjoint.comp A) (x y : E) :
    inner ℂ (A.adjoint x) (B.adjoint y) = inner ℂ (B x) (A y) := by
  rw [A.adjoint_inner_left]
  have hc := congrArg (fun L : E →L[ℂ] E => L y) h
  simp only [ContinuousLinearMap.comp_apply] at hc
  rw [hc, B.adjoint_inner_right]

theorem normal_adjoint_norm_sq (A : E →L[ℂ] E)
    (h : A.comp A.adjoint = A.adjoint.comp A) (x : E) :
    ‖A.adjoint x‖ ^ 2 = ‖A x‖ ^ 2 := by
  have hi := commuting_adjoint_inner A A h x x
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact congrArg RCLike.re hi

/-- Curl/divergence energy identity for three commuting normal directional
operators. It supplies the sharp Euclidean bound needed by Taylor estimates. -/
theorem commuting_curl_energy (A : Fin 3 → E →L[ℂ] E)
    (h : ∀ i j, (A i).comp (A j).adjoint = (A j).adjoint.comp (A i))
    (x : Fin 3 → E) :
    ‖A 1 (x 2) - A 2 (x 1)‖ ^ 2 +
      ‖A 2 (x 0) - A 0 (x 2)‖ ^ 2 +
      ‖A 0 (x 1) - A 1 (x 0)‖ ^ 2 +
      ‖(A 0).adjoint (x 0) + (A 1).adjoint (x 1) + (A 2).adjoint (x 2)‖ ^ 2 =
      ∑ i, ∑ j, ‖A i (x j)‖ ^ 2 := by
  have h01 := congrArg RCLike.re (commuting_adjoint_inner (A 0) (A 1) (h 0 1) (x 0) (x 1))
  have h02 := congrArg RCLike.re (commuting_adjoint_inner (A 0) (A 2) (h 0 2) (x 0) (x 2))
  have h12 := congrArg RCLike.re (commuting_adjoint_inner (A 1) (A 2) (h 1 2) (x 1) (x 2))
  have hn0 := normal_adjoint_norm_sq (A 0) (h 0 0) (x 0)
  have hn1 := normal_adjoint_norm_sq (A 1) (h 1 1) (x 1)
  have hn2 := normal_adjoint_norm_sq (A 2) (h 2 2) (x 2)
  simp only [norm_sub_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), inner_add_left,
    map_add, Fin.sum_univ_three]
  rw [h01, h02, h12, hn0, hn1, hn2]
  have hsym01 : RCLike.re (inner ℂ (A 1 (x 0)) (A 0 (x 1))) =
      RCLike.re (inner ℂ (A 0 (x 1)) (A 1 (x 0))) := by
    exact inner_re_symm _ _
  have hsym12 : RCLike.re (inner ℂ (A 2 (x 1)) (A 1 (x 2))) =
      RCLike.re (inner ℂ (A 1 (x 2)) (A 2 (x 1))) := by
    exact inner_re_symm _ _
  rw [hsym01, hsym12]
  ring

theorem commuting_curl_energy_le (A : Fin 3 → E →L[ℂ] E)
    (h : ∀ i j, (A i).comp (A j).adjoint = (A j).adjoint.comp (A i))
    (b : Fin 3 → ℝ) (hA : ∀ i, ‖A i‖ ≤ b i)
    (x : Fin 3 → E) :
    ‖A 1 (x 2) - A 2 (x 1)‖ ^ 2 +
      ‖A 2 (x 0) - A 0 (x 2)‖ ^ 2 +
      ‖A 0 (x 1) - A 1 (x 0)‖ ^ 2 ≤
      (∑ i, (b i) ^ 2) * ∑ j, ‖x j‖ ^ 2 := by
  have he := commuting_curl_energy A h x
  have hterms : (∑ i, ∑ j, ‖A i (x j)‖ ^ 2) ≤
      (∑ i, (b i) ^ 2) * ∑ j, ‖x j‖ ^ 2 := by
    calc
      _ ≤ ∑ i, ∑ j, (b i) ^ 2 * ‖x j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        have hn : ‖A i (x j)‖ ≤ b i * ‖x j‖ :=
          ((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
  have hd := sq_nonneg ‖(A 0).adjoint (x 0) + (A 1).adjoint (x 1) + (A 2).adjoint (x 2)‖
  linarith

end Operators

section Matrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def curlBlock (D : Fin 3 → Matrix ι ι ℂ) :
    Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ := fun i j =>
  if i.1 = 0 then
    if j.1 = 2 then D 1 i.2 j.2 else if j.1 = 1 then -D 2 i.2 j.2 else 0
  else if i.1 = 1 then
    if j.1 = 0 then D 2 i.2 j.2 else if j.1 = 2 then -D 0 i.2 j.2 else 0
  else
    if j.1 = 1 then D 0 i.2 j.2 else if j.1 = 0 then -D 1 i.2 j.2 else 0

noncomputable def componentVector (x : EuclideanSpace ℂ (Fin 3 × ι))
    (d : Fin 3) : EuclideanSpace ℂ ι := WithLp.toLp 2 fun i => x (d, i)

omit [DecidableEq ι] in
theorem componentVector_norm_sq (x : EuclideanSpace ℂ (Fin 3 × ι)) :
    (∑ d, ‖componentVector x d‖ ^ 2) = ‖x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, componentVector]

theorem curlBlock_action (D : Fin 3 → Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ (Fin 3 × ι)) :
    componentVector (Matrix.toEuclideanCLM (n := Fin 3 × ι) (𝕜 := ℂ) (curlBlock D) x) =
      ![Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (D 1) (componentVector x 2) -
          Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (D 2) (componentVector x 1),
        Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (D 2) (componentVector x 0) -
          Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (D 0) (componentVector x 2),
        Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (D 0) (componentVector x 1) -
          Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (D 1) (componentVector x 0)] := by
  funext d
  ext i
  fin_cases d <;>
    simp [componentVector, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_three, curlBlock]
  all_goals ring

theorem matrix_double_commutation
    (D : Fin 3 → Matrix ι ι ℂ)
    (h : ∀ i j, Commute (D i) (D j).conjTranspose) :
    ∀ i j,
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (D i)).comp
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (D j)).adjoint =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (D j)).adjoint.comp
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (D i)) := by
  intro i j
  have hm := congrArg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (h i j).eq
  change Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (D i * star (D j)) =
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (star (D j) * D i) at hm
  simpa only [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.mul_def] using hm

/-- The true Euclidean operator norm of the complete three-component curl,
with the sharp square-sum directional bound. -/
theorem curlBlock_norm_le (D : Fin 3 → Matrix ι ι ℂ)
    (h : ∀ i j, Commute (D i) (D j).conjTranspose)
    (b : Fin 3 → ℝ)
    (hD : ∀ i, ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (D i)‖ ≤ b i) :
    ‖Matrix.toEuclideanCLM (n := Fin 3 × ι) (𝕜 := ℂ) (curlBlock D)‖ ≤
      Real.sqrt (∑ i, (b i) ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (b i))]
  rw [← componentVector_norm_sq]
  rw [curlBlock_action]
  have he := commuting_curl_energy_le
    (fun i => Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (D i))
    (matrix_double_commutation D h) b hD (componentVector x)
  rw [componentVector_norm_sq] at he
  simpa [Fin.sum_univ_three] using he

end Matrices

end Maxwell.Spectral
