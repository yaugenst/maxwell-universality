import Maxwell.Defect.RankOneBlocks
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Complementary spectral gap of the actual first-order block reference.
The P and Q components are the coordinate projections of the original
diagonal spectral basis; no reference-gap premise is assumed. -/

namespace Maxwell.Defect
noncomputable section
open Matrix
open scoped Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Projection onto the possibly repeated selected eigenvalue. -/
def spectralP (d : ι → ℝ) (lam : ℝ) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (spectralPart d lam (WithLp.ofLp x))

def spectralQ (d : ι → ℝ) (lam : ℝ) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  x - spectralP d lam x

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem spectralP_apply (d : ι → ℝ) (lam : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) :
    spectralP d lam x i = if d i = lam then x i else 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem spectralQ_apply (d : ι → ℝ) (lam : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) :
    spectralQ d lam x i = if d i = lam then 0 else x i := by
  by_cases hi : d i = lam <;> simp [spectralQ, hi]

omit [Fintype ι] [DecidableEq ι] in
theorem spectralP_add_Q (d : ι → ℝ) (lam : ℝ) (x : EuclideanSpace ℝ ι) :
    spectralP d lam x + spectralQ d lam x = x := by simp [spectralQ]

omit [DecidableEq ι] in
theorem spectralP_Q_orthogonal (d : ι → ℝ) (lam : ℝ) (x y : EuclideanSpace ℝ ι) :
    inner ℝ (spectralP d lam x) (spectralQ d lam y) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : d i = lam <;> simp [star, spectralP_apply, spectralQ_apply, hi]

omit [DecidableEq ι] in
theorem spectral_norm_split (d : ι → ℝ) (lam : ℝ) (x : EuclideanSpace ℝ ι) :
    ‖x‖^2 = ‖spectralP d lam x‖^2 + ‖spectralQ d lam x‖^2 := by
  have h := norm_add_sq_real (spectralP d lam x) (spectralQ d lam x)
  simpa [spectralP_add_Q, spectralP_Q_orthogonal] using h

omit [DecidableEq ι] in
theorem spectralP_inner (d : ι → ℝ) (lam : ℝ) (w x : EuclideanSpace ℝ ι) :
    inner ℝ (spectralP d lam w) x =
      inner ℝ (spectralP d lam w) (spectralP d lam x) := by
  nth_rw 1 [← spectralP_add_Q d lam x]
  rw [inner_add_right, spectralP_Q_orthogonal, add_zero]

omit [DecidableEq ι] in
theorem spectralQ_inner (d : ι → ℝ) (lam : ℝ) (w x : EuclideanSpace ℝ ι) :
    inner ℝ (spectralQ d lam w) x =
      inner ℝ (spectralQ d lam w) (spectralQ d lam x) := by
  nth_rw 1 [← spectralP_add_Q d lam x]
  have ho : inner ℝ (spectralQ d lam w) (spectralP d lam x) = 0 := by
    rw [real_inner_comm]
    exact spectralP_Q_orthogonal d lam x w
  rw [inner_add_right, ho, zero_add]

/-- The actual block matrix after first-order cross-block elimination. -/
def blockReference (d : ι → ℝ) (lam δ : ℝ) (w : EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  Matrix.diagonal d - δ •
    (Matrix.vecMulVec (WithLp.ofLp (spectralP d lam w)) (WithLp.ofLp (spectralP d lam w)) +
     Matrix.vecMulVec (WithLp.ofLp (spectralQ d lam w)) (WithLp.ofLp (spectralQ d lam w)))

theorem rankOneMatrix_apply (a x : EuclideanSpace ℝ ι) :
    (Matrix.vecMulVec (WithLp.ofLp a) (WithLp.ofLp a)).toEuclideanLin x =
      (inner ℝ a x) • a := by
  ext i
  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.vecMulVec,
    Matrix.of_apply, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem blockReference_apply (d : ι → ℝ) (lam δ : ℝ) (w x : EuclideanSpace ℝ ι) :
    (blockReference d lam δ w).toEuclideanLin x =
      (Matrix.diagonal d).toEuclideanLin x -
        (δ * inner ℝ (spectralP d lam w) x) • spectralP d lam w -
        (δ * inner ℝ (spectralQ d lam w) x) • spectralQ d lam w := by
  simp only [blockReference, map_sub, map_smul, map_add, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.add_apply, rankOneMatrix_apply, smul_add, smul_smul]
  abel

@[simp] theorem diagonal_euclidean_apply (d : ι → ℝ) (x : EuclideanSpace ℝ ι) (i : ι) :
    (Matrix.diagonal d).toEuclideanLin x i = d i * x i := by
  simp [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

theorem diagonal_spectralP (d : ι → ℝ) (lam : ℝ) (w : EuclideanSpace ℝ ι) :
    (Matrix.diagonal d).toEuclideanLin (spectralP d lam w) = lam • spectralP d lam w := by
  ext i
  by_cases hi : d i = lam <;> simp [hi]

/-- The selected direction is an exact eigenvector of the complete reference. -/
theorem blockReference_selected (d : ι → ℝ) (lam δ : ℝ) (w : EuclideanSpace ℝ ι) :
    (blockReference d lam δ w).toEuclideanLin (spectralP d lam w) =
      (lam - δ * ‖spectralP d lam w‖^2) • spectralP d lam w := by
  have ho : inner ℝ (spectralQ d lam w) (spectralP d lam w) = 0 := by
    rw [real_inner_comm]
    exact spectralP_Q_orthogonal d lam w w
  rw [blockReference_apply, diagonal_spectralP, ho]
  simp [sub_smul]

/-- On the selected eigenspace orthogonal to the selected direction, the
reference residual is precisely the first-order spectral splitting. -/
theorem blockReference_P_residual (d : ι → ℝ) (lam δ : ℝ) (w x : EuclideanSpace ℝ ι)
    (hx : inner ℝ (spectralP d lam w) x = 0) :
    spectralP d lam ((blockReference d lam δ w).toEuclideanLin x -
      (lam - δ * ‖spectralP d lam w‖^2) • x) =
        (δ * ‖spectralP d lam w‖^2) • spectralP d lam x := by
  ext i
  by_cases hi : d i = lam
  · simp [spectralP_apply, blockReference_apply, hx, hi]
    ring
  · simp [spectralP_apply, hi]

/-- Exact residual formula on the complementary spectral block. -/
theorem blockReference_Q_residual (d : ι → ℝ) (lam δ : ℝ) (w x : EuclideanSpace ℝ ι) :
    spectralQ d lam ((blockReference d lam δ w).toEuclideanLin x -
      (lam - δ * ‖spectralP d lam w‖^2) • x) =
      (Matrix.diagonal d).toEuclideanLin (spectralQ d lam x) - lam • spectralQ d lam x +
        (δ * ‖spectralP d lam w‖^2) • spectralQ d lam x -
        (δ * inner ℝ (spectralQ d lam w) (spectralQ d lam x)) • spectralQ d lam w := by
  rw [← spectralQ_inner d lam w x]
  ext i
  by_cases hi : d i = lam
  · simp [spectralQ_apply, hi]
  · simp [spectralQ_apply, spectralP_apply, blockReference_apply, hi]
    ring

/-- The original off-block eigenvalue distances imply a genuine operator
lower bound on the Q block. -/
theorem diagonal_Q_gap (d : ι → ℝ) (lam G : ℝ) (x : EuclideanSpace ℝ ι)
    (hG : 0 ≤ G) (hgap : ∀ i, d i ≠ lam → G ≤ |d i - lam|) :
    G * ‖spectralQ d lam x‖ ≤
      ‖(Matrix.diagonal d).toEuclideanLin (spectralQ d lam x) - lam • spectralQ d lam x‖ := by
  have hcoord (i : ι) :
      G^2 * (spectralQ d lam x i)^2 ≤
        (((Matrix.diagonal d).toEuclideanLin (spectralQ d lam x) -
          lam • spectralQ d lam x) i)^2 := by
    by_cases hi : d i = lam
    · simp [spectralQ_apply, hi]
    · have hd := hgap i hi
      have hsq : G^2 ≤ (d i - lam)^2 := by
        nlinarith [sq_abs (d i - lam), abs_nonneg (d i - lam)]
      have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg (spectralQ d lam x i))
      simpa only [PiLp.sub_apply, PiLp.smul_apply, diagonal_euclidean_apply,
        smul_eq_mul, ← sub_mul, mul_pow] using hh
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord i)
  rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq,
    ← EuclideanSpace.real_norm_sq_eq] at hs
  nlinarith [norm_nonneg ((Matrix.diagonal d).toEuclideanLin (spectralQ d lam x) -
    lam • spectralQ d lam x), mul_nonneg hG (norm_nonneg (spectralQ d lam x))]

omit [DecidableEq ι] in
/-- The Q-block rank-one term has the squared-vector norm expected by the
first-order gap budget. -/
theorem rankOne_action_norm_le (b y : EuclideanSpace ℝ ι) (δ : ℝ) (hδ : 0 ≤ δ) :
    ‖(δ * inner ℝ b y) • b‖ ≤ δ * ‖b‖^2 * ‖y‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hδ]
  calc
    δ * |inner ℝ b y| * ‖b‖ ≤ δ * (‖b‖ * ‖y‖) * ‖b‖ := by
      gcongr
      exact abs_real_inner_le_norm b y
    _ = δ * ‖b‖^2 * ‖y‖ := by ring

/-- The Q-block gap loses at most the two explicit rank-one/target-shift
terms. The selected P-block is not counted in this estimate. -/
theorem blockReference_Q_gap (d : ι → ℝ) (lam δ G : ℝ) (w x : EuclideanSpace ℝ ι)
    (hδ : 0 ≤ δ) (hG : 0 ≤ G) (hgap : ∀ i, d i ≠ lam → G ≤ |d i - lam|) :
    (G - δ * ‖spectralP d lam w‖^2 - δ * ‖spectralQ d lam w‖^2) *
      ‖spectralQ d lam x‖ ≤
        ‖spectralQ d lam ((blockReference d lam δ w).toEuclideanLin x -
          (lam - δ * ‖spectralP d lam w‖^2) • x)‖ := by
  rw [blockReference_Q_residual]
  let y := spectralQ d lam x
  let a := spectralP d lam w
  let b := spectralQ d lam w
  let z := (Matrix.diagonal d).toEuclideanLin y - lam • y
  let v := (δ * ‖a‖^2) • y
  let u := (δ * inner ℝ b y) • b
  change (G - δ * ‖a‖^2 - δ * ‖b‖^2) * ‖y‖ ≤ ‖z + v - u‖
  have hz : G * ‖y‖ ≤ ‖z‖ := diagonal_Q_gap d lam G x hG hgap
  have hv : ‖v‖ = δ * ‖a‖^2 * ‖y‖ := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hδ (sq_nonneg _))]
  have hu : ‖u‖ ≤ δ * ‖b‖^2 * ‖y‖ := rankOne_action_norm_le b y δ hδ
  have ht : ‖z‖ ≤ ‖z + v - u‖ + (‖u‖ + ‖v‖) := by
    have heq : z = (z + v - u) + (u - v) := by abel
    calc
      ‖z‖ = ‖(z + v - u) + (u - v)‖ := by rw [← heq]
      _ ≤ ‖z + v - u‖ + ‖u - v‖ := norm_add_le _ _
      _ ≤ ‖z + v - u‖ + (‖u‖ + ‖v‖) :=
        add_le_add (le_refl _) (norm_sub_le _ _)
  rw [hv] at ht
  nlinarith

/-- The complete reference has a linear complementary gap. Its proof
combines the P and Q bounds by their orthogonal norm squares. -/
theorem blockReference_complementary_gap (d : ι → ℝ) (lam δ G : ℝ)
    (w x : EuclideanSpace ℝ ι) (hδ : 0 ≤ δ) (hG : 0 ≤ G)
    (hgap : ∀ i, d i ≠ lam → G ≤ |d i - lam|)
    (hsmall : δ * (2 * ‖spectralP d lam w‖^2 + ‖spectralQ d lam w‖^2) ≤ G)
    (hx : inner ℝ (spectralP d lam w) x = 0) :
    (δ * ‖spectralP d lam w‖^2) * ‖x‖ ≤
      ‖(blockReference d lam δ w).toEuclideanLin x -
        (lam - δ * ‖spectralP d lam w‖^2) • x‖ := by
  let g := δ * ‖spectralP d lam w‖^2
  let r := (blockReference d lam δ w).toEuclideanLin x -
    (lam - δ * ‖spectralP d lam w‖^2) • x
  have hg : 0 ≤ g := mul_nonneg hδ (sq_nonneg _)
  have hP : ‖spectralP d lam r‖ = g * ‖spectralP d lam x‖ := by
    dsimp [r]
    rw [blockReference_P_residual d lam δ w x hx, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hg]
  have hQ : g * ‖spectralQ d lam x‖ ≤ ‖spectralQ d lam r‖ := by
    have hbase := blockReference_Q_gap d lam δ G w x hδ hG hgap
    have hcoef : g ≤ G - δ * ‖spectralP d lam w‖^2 - δ * ‖spectralQ d lam w‖^2 := by
      dsimp [g]
      nlinarith
    exact (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)).trans hbase
  have hQsquared : g^2 * ‖spectralQ d lam x‖^2 ≤ ‖spectralQ d lam r‖^2 := by
    nlinarith [mul_nonneg hg (norm_nonneg (spectralQ d lam x)),
      norm_nonneg (spectralQ d lam r)]
  have hPsquared : g^2 * ‖spectralP d lam x‖^2 = ‖spectralP d lam r‖^2 := by
    rw [hP]; ring
  have hxsplit := spectral_norm_split d lam x
  have hrsplit := spectral_norm_split d lam r
  have hnormsq : g^2 * ‖x‖^2 ≤ ‖r‖^2 := by
    rw [hxsplit, hrsplit, mul_add, hPsquared]
    linarith
  change g * ‖x‖ ≤ ‖r‖
  nlinarith [mul_nonneg hg (norm_nonneg x), norm_nonneg r]

/-- The normalized vector and complete complementary-gap package needed
by `isolated_eigenpair_stability`. -/
theorem blockReference_unit_reference (d : ι → ℝ) (lam δ G : ℝ)
    (w : EuclideanSpace ℝ ι) (ha : spectralP d lam w ≠ 0)
    (hδ : 0 ≤ δ) (hG : 0 ≤ G)
    (hgap : ∀ i, d i ≠ lam → G ≤ |d i - lam|)
    (hsmall : δ * (2 * ‖spectralP d lam w‖^2 + ‖spectralQ d lam w‖^2) ≤ G) :
    let a := spectralP d lam w
    let v := ‖a‖⁻¹ • a
    let μ := lam - δ * ‖a‖^2
    ‖v‖ = 1 ∧ (blockReference d lam δ w).toEuclideanLin v = μ • v ∧
      ∀ x : EuclideanSpace ℝ ι, inner ℝ v x = 0 →
        (δ * ‖a‖^2) * ‖x‖ ≤ ‖(blockReference d lam δ w).toEuclideanLin x - μ • x‖ := by
  dsimp only
  refine ⟨by simp [norm_smul, ha], ?_, ?_⟩
  · rw [map_smul, blockReference_selected, smul_comm]
  · intro x hx
    have hnorm : ‖spectralP d lam w‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    have hx' : inner ℝ (spectralP d lam w) x = 0 := by
      simp only [inner_smul_left, RCLike.conj_to_real] at hx
      exact (mul_eq_zero.mp hx).resolve_left (inv_ne_zero hnorm)
    exact blockReference_complementary_gap d lam δ G w x hδ hG hgap hsmall hx'

omit [Fintype ι] in
/-- Exact identification with the first-order block reference produced by
the Cayley commutator cancellation. -/
theorem blockReference_eq_blockPart (d : ι → ℝ) (lam c τ : ℝ)
    (w : EuclideanSpace ℝ ι) :
    blockReference d lam (c * τ) w = Matrix.diagonal d +
      τ • spectralBlockPart d lam (-c • Matrix.vecMulVec (WithLp.ofLp w) (WithLp.ofLp w)) := by
  rw [spectralBlockPart_rankOne]
  change Matrix.diagonal d - (c * τ) •
    (Matrix.vecMulVec (WithLp.ofLp (spectralP d lam w)) (WithLp.ofLp (spectralP d lam w)) +
      Matrix.vecMulVec (WithLp.ofLp (spectralQ d lam w)) (WithLp.ofLp (spectralQ d lam w))) = _
  have hP : spectralPart d lam (WithLp.ofLp w) = WithLp.ofLp (spectralP d lam w) := rfl
  have hQ : spectralComplement d lam (WithLp.ofLp w) = WithLp.ofLp (spectralQ d lam w) := rfl
  rw [hP, hQ]
  simp only [neg_smul, smul_neg, smul_smul, ← sub_eq_add_neg, mul_comm τ c]

end
end Maxwell.Defect
