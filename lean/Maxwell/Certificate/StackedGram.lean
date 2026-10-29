import Maxwell.Certificate.CurvatureTransfer

namespace Maxwell.Certificate.StackedGram
open Maxwell.Certificate.CorrectorWitness Maxwell.Certificate.CurvatureTransfer Matrix
noncomputable section
variable {ι κ H : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [DecidableEq ι] in
theorem synthesis_smul_columns (v : ι → H) (a : ℂ) :
    synthesis (fun p => a • v p) = a • synthesis v := by
  ext x
  simp only [synthesis_apply, _root_.smul_apply, Finset.smul_sum, smul_smul]
  congr 1
  ext p
  rw [mul_comm]

theorem synthesis_family_inner (v : κ → ι → H) (G : Matrix ι ι ℝ)
    (hG : ∀ p q, ∑ i, inner ℂ (v i p) (v i q) = (G p q : ℂ))
    (x : EuclideanSpace ℂ ι) :
    (∑ i, inner ℂ (synthesis (v i) x) (synthesis (v i) x)) =
      inner ℂ x (realMatrixOperator G x) := by
  simp only [synthesis_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  change (∑ i, ∑ q, x q * ∑ p, starRingEnd ℂ (x p) * inner ℂ (v i p) (v i q)) =
    star (fun i => x i) ⬝ᵥ ((G.map Complex.ofReal) *ᵥ fun i => x i)
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.mul_sum, ← Finset.mul_sum, hG]
  simp only [Complex.star_def]
  ring

theorem synthesis_family_norm_sq (v : κ → ι → H) (G : Matrix ι ι ℝ)
    (hG : ∀ p q, ∑ i, inner ℂ (v i p) (v i q) = (G p q : ℂ))
    (x : EuclideanSpace ℂ ι) :
    (∑ i, ‖synthesis (v i) x‖^2) =
      Complex.re (inner ℂ x (realMatrixOperator G x)) := by
  have h := congrArg Complex.re (synthesis_family_inner v G hG x)
  rw [Complex.re_sum] at h
  have hn (i : κ) : (inner ℂ (synthesis (v i) x) (synthesis (v i) x)).re =
      ‖synthesis (v i) x‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  simpa only [hn] using h

theorem realMatrixOperator_smul_quadratic (G : Matrix ι ι ℝ) (a : ℝ)
    (x : EuclideanSpace ℂ ι) :
    Complex.re (inner ℂ x (realMatrixOperator (a • G) x)) =
      a * Complex.re (inner ℂ x (realMatrixOperator G x)) := by
  rw [realMatrixOperator_quadratic, realMatrixOperator_quadratic]
  simp only [smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

/-- A real enclosure of the scalar physical prefactor bounds the full
stacked Gram form; positivity comes from the actual vector synthesis. -/
theorem scaled_synthesis_family_bound (v : κ → ι → H) (G : Matrix ι ι ℝ)
    (hG : ∀ p q, ∑ i, inner ℂ (v i p) (v i q) = (G p q : ℂ))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (x : EuclideanSpace ℂ ι) :
    (∑ i, ‖((a : ℂ) • synthesis (v i)) x‖^2) ≤
      Complex.re (inner ℂ x (realMatrixOperator (b^2 • G) x)) := by
  have hb : 0 ≤ b := ha.trans hab
  have hs := synthesis_family_norm_sq v G hG x
  have hp : 0 ≤ Complex.re (inner ℂ x (realMatrixOperator G x)) := by
    rw [← hs]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [_root_.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, ← Finset.mul_sum]
  rw [hs, realMatrixOperator_smul_quadratic]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 2) hp

theorem scaled_column_family_bound (v : κ → ι → H) (G : Matrix ι ι ℝ)
    (hG : ∀ p q, ∑ i, inner ℂ (v i p) (v i q) = (G p q : ℂ))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (x : EuclideanSpace ℂ ι) :
    (∑ i, ‖synthesis (fun p => (a : ℂ) • v i p) x‖^2) ≤
      Complex.re (inner ℂ x (realMatrixOperator (b^2 • G) x)) := by
  simp only [synthesis_smul_columns]
  exact scaled_synthesis_family_bound v G hG a b ha hab x

end
end Maxwell.Certificate.StackedGram
