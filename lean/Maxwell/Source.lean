import Maxwell.Interfaces
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact square rational input and Euclidean error conventions.

These are definitions of the paper's input contract, not existence assumptions
about a compiler. An input's requested accuracy is not an algorithmic input:
the encoder may use the fixed promise exponent instead.
-/

namespace Maxwell

open Matrix
open scoped Matrix

/-- Euclidean operator condition number; nonsingularity is a separate promise. -/
noncomputable def condition₂ {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    (A : Matrix ι ι 𝕜) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) A‖ *
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) A⁻¹‖

namespace Source

/-- Explicit finite rational data. Coordinate validity and unique sparse
storage are enforced by `SparseRationalMatrix`, not unchecked parser promises. -/
structure SparseSystem where
  n : ℕ
  matrix : SparseRationalMatrix n n
  source : Fin n → ℚ

def SparseSystem.nnz (S : SparseSystem) : ℕ := S.matrix.nnz

noncomputable def realMatrix (S : SparseSystem) : Matrix (Fin S.n) (Fin S.n) ℝ :=
  S.matrix.toMatrix.map fun q => (q : ℝ)

noncomputable def operator (S : SparseSystem) :
    EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n) :=
  Matrix.toEuclideanCLM (n := Fin S.n) (𝕜 := ℝ) (realMatrix S)

noncomputable def rhs (S : SparseSystem) : EuclideanSpace ℝ (Fin S.n) :=
  WithLp.toLp 2 fun i => (S.source i : ℝ)

noncomputable def rationalVector {n : ℕ} (x : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => (x i : ℝ)

/-- The residual convention of the square rational source theorem. -/
def ResidualTarget (S : SparseSystem) (eta : ℝ) (x : Fin S.n → ℚ) : Prop :=
  ‖operator S (rationalVector x) - rhs S‖ ≤ eta * ‖rhs S‖

/-- Fixed positive promise parameters. No physical or algorithmic conclusion
is a field of this structure. The bit budget uses the natural logarithm. -/
structure Parameters where
  conditionExponent : ℝ
  accuracyExponent : ℝ
  inputBitFactor : ℝ
  conditionExponent_pos : 0 < conditionExponent
  accuracyExponent_pos : 0 < accuracyExponent
  inputBitFactor_pos : 0 < inputBitFactor

/-- Numerator and denominator bounds are separate, as in the paper. -/
def ShortRational (budget : ℝ) (q : ℚ) : Prop :=
  (signedBitLength q.num : ℝ) ≤ budget ∧
    (unsignedBitLength q.den : ℝ) ≤ budget

noncomputable def bitBudget (p : Parameters) (S : SparseSystem) : ℝ :=
  p.inputBitFactor * Real.log (2 + (S.nnz : ℝ))

/-- The source's nonsingularity, conditioning, and coefficient/source promises. -/
def Promises (p : Parameters) (S : SparseSystem) : Prop :=
  IsUnit (realMatrix S) ∧
    condition₂ (realMatrix S) ≤ (S.nnz : ℝ) ^ p.conditionExponent ∧
    (∀ i j, ShortRational (bitBudget p S) (S.matrix.toMatrix i j)) ∧
    (∀ i, ShortRational (bitBudget p S) (S.source i))

/-- Accuracy is a mathematical requested target, not an unbounded encoded
real word that the encoder is entitled to read for free. -/
def RequestedAccuracy (p : Parameters) (S : SparseSystem) (eta : ℝ) : Prop :=
  (S.nnz : ℝ) ^ (-p.accuracyExponent) ≤ eta ∧ eta ≤ 1

noncomputable def fixedAccuracy (p : Parameters) (S : SparseSystem) : ℝ :=
  (S.nnz : ℝ) ^ (-(Nat.ceil p.accuracyExponent : ℝ))

/-- The fixed integer promise exponent suffices for every requested accuracy;
no machine needs access to the arbitrary real number `eta`. -/
theorem fixedAccuracy_le_requested (p : Parameters) (S : SparseSystem)
    (hm : 1 ≤ S.nnz) (eta : ℝ) (heta : RequestedAccuracy p S eta) :
    fixedAccuracy p S ≤ eta := by
  apply le_trans _ heta.1
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm)
    (neg_le_neg (Nat.le_ceil p.accuracyExponent))

/-- Nonsingularity forces at least one stored nonzero in every row. -/
theorem row_has_nonzero (S : SparseSystem) (hunit : IsUnit (realMatrix S))
    (i : Fin S.n) : ∃ j, S.matrix.toMatrix i j ≠ 0 := by
  rcases hunit with ⟨u, hu⟩
  have hinv : realMatrix S * (↑(u⁻¹) : Matrix (Fin S.n) (Fin S.n) ℝ) = 1 := by
    rw [← hu]
    simp
  by_contra hnone
  push Not at hnone
  have hrow : ∀ j, realMatrix S i j = 0 := by
    intro j
    simp [realMatrix, hnone j]
  have hentry := congrArg (fun A : Matrix (Fin S.n) (Fin S.n) ℝ => A i i) hinv
  simp [Matrix.mul_apply, hrow] at hentry

/-- The full source vector can be read within the sparse-input size budget. -/
theorem dimension_le_nnz (S : SparseSystem) (hunit : IsUnit (realMatrix S)) : S.n ≤ S.nnz := by
  have himage : S.matrix.support.image Prod.fst = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    obtain ⟨j, hj⟩ := row_has_nonzero S hunit i
    exact Finset.mem_image.mpr ⟨(i, j),
      (SparseRationalMatrix.toMatrix_ne_zero_iff S.matrix i j).mp hj, rfl⟩
  calc
    S.n = (Finset.univ : Finset (Fin S.n)).card := by simp
    _ = (S.matrix.support.image Prod.fst).card := by rw [himage]
    _ ≤ S.nnz := Finset.card_image_le

/-- The empty-system corner is dealt with directly, without interpreting
the theorem's `1/m` probability bound at `m=0`. -/
theorem source_zero_of_nnz_zero (S : SparseSystem) (hunit : IsUnit (realMatrix S))
    (hm : S.nnz = 0) : S.source = 0 := by
  funext i
  have hn := dimension_le_nnz S hunit
  have hi := i.isLt
  omega

/-- The zero-source case has an exact rational output, independently of the
condition number or the requested tolerance. -/
theorem zero_source_residual (S : SparseSystem) (eta : ℝ)
    (hzero : S.source = 0) : ResidualTarget S eta 0 := by
  have hx : rationalVector (0 : Fin S.n → ℚ) = 0 := by ext i; simp [rationalVector]
  have hb : rhs S = 0 := by ext i; simp [rhs, hzero]
  simp [ResidualTarget, hx, hb]

end Source
end Maxwell
