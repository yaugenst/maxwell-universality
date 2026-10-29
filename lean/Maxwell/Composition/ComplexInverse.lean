import Maxwell.Probability.Spectral

/-! A real matrix acts on complex Euclidean space with exactly the same
induced norm. Consequently a real two-sided inverse certificate constructs
both Euclidean inverses with no change in the inverse norm bound. -/

noncomputable section
namespace Maxwell.Composition.ComplexInverse

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι]

def realPart (x : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => (x i).re)

def imagPart (x : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => (x i).im)

def ofRealVector (x : EuclideanSpace ℝ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => (x i : ℂ))

theorem norm_sq_parts (x : EuclideanSpace ℂ ι) :
    ‖x‖ ^ 2 = ‖realPart x‖ ^ 2 + ‖imagPart x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  change (∑ i, ‖x i‖ ^ 2) = (∑ i, (x i).re ^ 2) + ∑ i, (x i).im ^ 2
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

@[simp] theorem ofRealVector_norm (x : EuclideanSpace ℝ ι) : ‖ofRealVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [ofRealVector]

variable [DecidableEq ι]

def realOperator (A : Matrix ι ι ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A

def complexOperator (A : Matrix ι ι ℝ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (A.map Complex.ofReal)

theorem complexOperator_realPart (A : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    realPart (complexOperator A x) = realOperator A (realPart x) := by
  ext i
  change (∑ j, (A i j : ℂ) * x j).re = ∑ j, A i j * (x j).re
  simp

theorem complexOperator_imagPart (A : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    imagPart (complexOperator A x) = realOperator A (imagPart x) := by
  ext i
  change (∑ j, (A i j : ℂ) * x j).im = ∑ j, A i j * (x j).im
  simp

theorem complexOperator_ofReal (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    complexOperator A (ofRealVector x) = ofRealVector (realOperator A x) := by
  ext i
  change (∑ j, (A i j : ℂ) * (x j : ℂ)) = ((∑ j, A i j * x j : ℝ) : ℂ)
  simp

/-- The real and imaginary parts are orthogonal, so complexification costs
no factor in the Euclidean operator norm. -/
theorem complexOperator_norm_le (A : Matrix ι ι ℝ) :
    ‖complexOperator A‖ ≤ ‖realOperator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hr := pow_le_pow_left₀ (norm_nonneg _)
    ((realOperator A).le_opNorm (realPart x)) 2
  have hi := pow_le_pow_left₀ (norm_nonneg _)
    ((realOperator A).le_opNorm (imagPart x)) 2
  have hx := norm_sq_parts x
  have hy := norm_sq_parts (complexOperator A x)
  rw [complexOperator_realPart, complexOperator_imagPart] at hy
  have hsq : ‖complexOperator A x‖ ^ 2 ≤ (‖realOperator A‖ * ‖x‖) ^ 2 := by
    nlinarith only [hr, hi, hy, congrArg (fun t : ℝ => ‖realOperator A‖ ^ 2 * t) hx]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsq

theorem realOperator_norm_le (A : Matrix ι ι ℝ) :
    ‖realOperator A‖ ≤ ‖complexOperator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have h := (complexOperator A).le_opNorm (ofRealVector x)
  simpa only [complexOperator_ofReal, ofRealVector_norm] using h

theorem complexOperator_norm (A : Matrix ι ι ℝ) :
    ‖complexOperator A‖ = ‖realOperator A‖ :=
  le_antisymm (complexOperator_norm_le A) (realOperator_norm_le A)

theorem matrix_ofReal_norm (A : Matrix ι ι ℝ) : ‖A.map Complex.ofReal‖ = ‖A‖ :=
  complexOperator_norm A

/-- A concrete two-sided matrix inverse gives an actual Euclidean
continuous linear equivalence, for either real or complex scalars. -/
def matrixEquiv {𝕜 : Type*} [RCLike 𝕜] (A B : Matrix ι ι 𝕜)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    EuclideanSpace 𝕜 ι ≃L[𝕜] EuclideanSpace 𝕜 ι :=
  ContinuousLinearEquiv.equivOfInverse'
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) A)
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) B)
    (by
      change Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) A *
        Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) B = 1
      rw [← map_mul, hAB, map_one])
    (by
      change Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) B *
        Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) A = 1
      rw [← map_mul, hBA, map_one])

@[simp] theorem matrixEquiv_coe {𝕜 : Type*} [RCLike 𝕜] (A B : Matrix ι ι 𝕜)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    (matrixEquiv A B hAB hBA : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) A := rfl

@[simp] theorem matrixEquiv_symm_coe {𝕜 : Type*} [RCLike 𝕜] (A B : Matrix ι ι 𝕜)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    ((matrixEquiv A B hAB hBA).symm : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) B := rfl

def realEquiv (A : Matrix ι ι ℝ) {L : ℝ} (h : Probability.InverseBound A L) :
    EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι :=
  matrixEquiv A h.choose h.choose_spec.1 h.choose_spec.2.1

@[simp] theorem realEquiv_coe (A : Matrix ι ι ℝ) {L : ℝ} (h : Probability.InverseBound A L) :
    (realEquiv A h : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A := rfl

theorem realEquiv_inverse_norm_le (A : Matrix ι ι ℝ) {L : ℝ}
    (h : Probability.InverseBound A L) :
    ‖((realEquiv A h).symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ ≤ L :=
  h.choose_spec.2.2

theorem ofReal_mul_eq_one (A B : Matrix ι ι ℝ) (h : A * B = 1) :
    A.map Complex.ofReal * B.map Complex.ofReal = 1 := by
  change A.map Complex.ofRealHom * B.map Complex.ofRealHom = 1
  rw [← Matrix.map_mul, h]
  exact map_one (Complex.ofRealHom.mapMatrix : Matrix ι ι ℝ →+* Matrix ι ι ℂ)

def complexEquiv (A : Matrix ι ι ℝ) {L : ℝ} (h : Probability.InverseBound A L) :
    EuclideanSpace ℂ ι ≃L[ℂ] EuclideanSpace ℂ ι :=
  matrixEquiv (A.map Complex.ofReal) (h.choose.map Complex.ofReal)
    (ofReal_mul_eq_one A h.choose h.choose_spec.1)
    (ofReal_mul_eq_one h.choose A h.choose_spec.2.1)

@[simp] theorem complexEquiv_coe (A : Matrix ι ι ℝ) {L : ℝ} (h : Probability.InverseBound A L) :
    (complexEquiv A h : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (A.map Complex.ofReal) := rfl

theorem complexEquiv_inverse_norm_eq (A : Matrix ι ι ℝ) {L : ℝ}
    (h : Probability.InverseBound A L) :
    ‖((complexEquiv A h).symm : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)‖ =
      ‖((realEquiv A h).symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ :=
  complexOperator_norm h.choose

/-- The same numerical inverse bound holds for arbitrary complex vectors. -/
theorem complexEquiv_inverse_norm_le (A : Matrix ι ι ℝ) {L : ℝ}
    (h : Probability.InverseBound A L) :
    ‖((complexEquiv A h).symm : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)‖ ≤ L := by
  rw [complexEquiv_inverse_norm_eq]
  exact realEquiv_inverse_norm_le A h

end Maxwell.Composition.ComplexInverse
