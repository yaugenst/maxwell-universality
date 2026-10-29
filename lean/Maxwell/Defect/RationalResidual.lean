import Maxwell.Defect.RankOneResidual
import Maxwell.Certificate.Matrix

/-! Exact rational residual and quadratic-gap checks, interpreted as
certificates for real Euclidean operators. -/
namespace Maxwell.Defect

open InnerProductSpace Module.End Matrix

variable {n : ℕ}

def rationalNormSq (v : Fin n → ℚ) : ℚ := ∑ i, v i ^ 2

def rationalProjector (v : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  (rationalNormSq v)⁻¹ • Matrix.vecMulVec v v

def rationalReference (T : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) (μ : ℚ) :=
  (1 - rationalProjector v) * T * (1 - rationalProjector v) + μ • rationalProjector v

def rationalGapMatrix (T : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) (μ g : ℚ) :=
  let R := rationalReference T v μ - μ • 1
  R.transpose * R + (2 * g ^ 2) • rationalProjector v - (g ^ 2) • 1

def rationalResidualSq (T : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) (μ : ℚ) : ℚ :=
  ∑ i, ((T *ᵥ v) i - μ * v i) ^ 2

noncomputable def rationalVector (v : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (v i : ℝ))

noncomputable def rationalUnitVector (v : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) :=
  ‖rationalVector v‖⁻¹ • rationalVector v

noncomputable def rationalMatrixCast :
    Matrix (Fin n) (Fin n) ℚ →+* Matrix (Fin n) (Fin n) ℝ :=
  (Rat.castHom ℝ).mapMatrix

noncomputable def rationalOperator : Matrix (Fin n) (Fin n) ℚ →+*
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  euclideanOperator.toRingHom.comp rationalMatrixCast

@[simp] theorem rationalMatrixCast_apply (T : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    rationalMatrixCast T i j = (T i j : ℝ) := rfl

@[simp] theorem rationalMatrixCast_smul (c : ℚ) (T : Matrix (Fin n) (Fin n) ℚ) :
    rationalMatrixCast (c • T) = (c : ℝ) • rationalMatrixCast T := by
  ext i j
  simp [rationalMatrixCast, Matrix.smul_apply]

@[simp] theorem rationalOperator_smul (c : ℚ) (T : Matrix (Fin n) (Fin n) ℚ) :
    rationalOperator (c • T) = (c : ℝ) • rationalOperator T := by
  change euclideanOperator (rationalMatrixCast (c • T)) = _
  rw [rationalMatrixCast_smul, map_smul]
  rfl

@[simp] theorem rationalOperator_transpose (T : Matrix (Fin n) (Fin n) ℚ) :
    rationalOperator T.transpose = star (rationalOperator T) := by
  change euclideanOperator (rationalMatrixCast T).transpose = _
  exact euclideanOperator_transpose _

theorem rationalNormSq_cast (v : Fin n → ℚ) :
    (rationalNormSq v : ℝ) = ‖rationalVector v‖ ^ 2 := by
  simp [rationalNormSq, EuclideanSpace.real_norm_sq_eq, rationalVector]

theorem rationalVector_ne_zero (v : Fin n → ℚ) (hv : v ≠ 0) : rationalVector v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hi := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) h
  change (v i : ℝ) = 0 at hi
  change v i = 0
  exact_mod_cast hi

theorem rationalUnitVector_norm (v : Fin n → ℚ) (hv : v ≠ 0) :
    ‖rationalUnitVector v‖ = 1 := by
  rw [rationalUnitVector, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (rationalVector_ne_zero v hv))

theorem euclideanOperator_vecMulVec (v : EuclideanSpace ℝ (Fin n)) :
    euclideanOperator (Matrix.vecMulVec (WithLp.ofLp v) (WithLp.ofLp v)) =
      rankOne ℝ v v := by
  have h := Matrix.toEuclideanLin.apply_symm_apply (rankOne ℝ v v).toLinearMap
  rw [symm_toEuclideanLin_rankOne] at h
  apply ContinuousLinearMap.ext
  intro x
  change (Matrix.toEuclideanLin _) x = _
  simpa using congrArg (fun f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n) => f x) h

theorem rationalProjector_operator (v : Fin n → ℚ) :
    rationalOperator (rationalProjector v) =
      rankOne ℝ (rationalUnitVector v) (rationalUnitVector v) := by
  have hcast : rationalMatrixCast (Matrix.vecMulVec v v) =
      Matrix.vecMulVec (WithLp.ofLp (rationalVector v)) (WithLp.ofLp (rationalVector v)) := by
    ext i j
    simp [Matrix.vecMulVec, rationalVector]
  rw [rationalProjector, rationalOperator_smul]
  change (↑((rationalNormSq v)⁻¹) : ℝ) • euclideanOperator (rationalMatrixCast _) = _
  rw [hcast, euclideanOperator_vecMulVec, Rat.cast_inv, rationalNormSq_cast]
  apply ContinuousLinearMap.ext
  intro x
  simp only [_root_.smul_apply, rankOne_apply, rationalUnitVector,
    inner_smul_left, conj_trivial, smul_smul]
  congr 1
  ring

theorem rationalReference_operator (T : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → ℚ) (μ : ℚ) :
    rationalOperator (rationalReference T v μ) =
      residualReference (rationalOperator T) (rationalUnitVector v) μ := by
  simp only [rationalReference, map_add, map_mul, map_sub, map_one,
    rationalOperator_smul, rationalProjector_operator, residualReference]

theorem rationalProjector_isSymm (v : Fin n → ℚ) : (rationalProjector v).IsSymm := by
  change (rationalProjector v).transpose = rationalProjector v
  simp [rationalProjector, Matrix.transpose_smul, Matrix.transpose_vecMulVec]

theorem rationalGapMatrix_isSymm (T : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → ℚ) (μ g : ℚ) : (rationalGapMatrix T v μ g).IsSymm := by
  change (rationalGapMatrix T v μ g).transpose = rationalGapMatrix T v μ g
  simp only [rationalGapMatrix, Matrix.transpose_sub, Matrix.transpose_add,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_smul,
    Matrix.transpose_one, (rationalProjector_isSymm v).eq]

theorem rationalOperator_vector (T : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) :
    rationalOperator T (rationalVector v) = rationalVector (T *ᵥ v) := by
  ext i
  change ((rationalMatrixCast T) *ᵥ (fun j => (v j : ℝ))) i = ((T *ᵥ v) i : ℝ)
  simp [Matrix.mulVec, dotProduct]

theorem rationalResidualSq_cast (T : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → ℚ) (μ : ℚ) :
    (rationalResidualSq T v μ : ℝ) =
      ‖rationalOperator T (rationalVector v) - (μ : ℝ) • rationalVector v‖ ^ 2 := by
  rw [rationalOperator_vector, EuclideanSpace.real_norm_sq_eq]
  simp [rationalResidualSq, rationalVector]

theorem rationalResidual_bound (T : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → ℚ) (μ ε : ℚ) (hv : v ≠ 0) (hε : 0 ≤ ε)
    (hcheck : rationalResidualSq T v μ ≤ ε ^ 2 * rationalNormSq v) :
    ‖rationalOperator T (rationalUnitVector v) - (μ : ℝ) • rationalUnitVector v‖ ≤
      (ε : ℝ) := by
  have hn := norm_pos_iff.mpr (rationalVector_ne_zero v hv)
  have he : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have hsq : ‖rationalOperator T (rationalVector v) - (μ : ℝ) • rationalVector v‖ ^ 2 ≤
      (ε : ℝ) ^ 2 * ‖rationalVector v‖ ^ 2 := by
    rw [← rationalResidualSq_cast, ← rationalNormSq_cast]
    exact_mod_cast hcheck
  have hb : ‖rationalOperator T (rationalVector v) - (μ : ℝ) • rationalVector v‖ ≤
      (ε : ℝ) * ‖rationalVector v‖ := by
    nlinarith [norm_nonneg (rationalOperator T (rationalVector v) -
      (μ : ℝ) • rationalVector v), mul_nonneg he hn.le]
  have hr : rationalOperator T (rationalUnitVector v) - (μ : ℝ) • rationalUnitVector v =
      ‖rationalVector v‖⁻¹ •
        (rationalOperator T (rationalVector v) - (μ : ℝ) • rationalVector v) := by
    simp only [rationalUnitVector, map_smul, smul_sub]
    module
  rw [hr, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  calc
    _ ≤ ‖rationalVector v‖⁻¹ * ((ε : ℝ) * ‖rationalVector v‖) := by gcongr
    _ = ε := by field_simp

theorem rationalResidualSq_normalized (T : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → ℚ) (μ : ℚ) (hv : v ≠ 0) :
    (rationalResidualSq T v μ : ℝ) =
      ‖rationalOperator T (rationalUnitVector v) - (μ : ℝ) • rationalUnitVector v‖ ^ 2 *
        (rationalNormSq v : ℝ) := by
  have hn := norm_ne_zero_iff.mpr (rationalVector_ne_zero v hv)
  have hs : ‖rationalVector v‖ • rationalUnitVector v = rationalVector v := by
    simp [rationalUnitVector, smul_smul, hn]
  have hr : rationalOperator T (rationalVector v) - (μ : ℝ) • rationalVector v =
      ‖rationalVector v‖ •
        (rationalOperator T (rationalUnitVector v) - (μ : ℝ) • rationalUnitVector v) := by
    rw [smul_sub, ← map_smul, hs, smul_comm, hs]
  rw [rationalResidualSq_cast, hr, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), mul_pow, rationalNormSq_cast]
  ring

theorem rationalResidual_bound_iff (T : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → ℚ) (μ ε : ℚ) (hv : v ≠ 0) (hε : 0 ≤ ε) :
    rationalResidualSq T v μ ≤ ε ^ 2 * rationalNormSq v ↔
      ‖rationalOperator T (rationalUnitVector v) - (μ : ℝ) • rationalUnitVector v‖ ≤
        (ε : ℝ) := by
  refine ⟨rationalResidual_bound T v μ ε hv hε, fun h => ?_⟩
  have hs : ‖rationalOperator T (rationalUnitVector v) - (μ : ℝ) • rationalUnitVector v‖ ^ 2 ≤
      (ε : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hc : (rationalResidualSq T v μ : ℝ) ≤ (ε : ℝ) ^ 2 * (rationalNormSq v : ℝ) := by
    rw [rationalResidualSq_normalized T v μ hv]
    exact mul_le_mul_of_nonneg_right hs (rationalNormSq_cast v ▸ sq_nonneg _)
  exact_mod_cast hc

theorem rationalOperator_symmetric (T : Matrix (Fin n) (Fin n) ℚ) (hT : T.IsSymm) :
    (rationalOperator T).toLinearMap.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  apply Matrix.isHermitian_iff_isSymm.mpr
  change (rationalMatrixCast T).transpose = rationalMatrixCast T
  change rationalMatrixCast T.transpose = rationalMatrixCast T
  rw [hT.eq]

theorem rationalGapMatrix_operator (T : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → ℚ) (μ g : ℚ) :
    let A := residualReference (rationalOperator T) (rationalUnitVector v) (μ : ℝ)
    let R := A - (μ : ℝ) • 1
    rationalOperator (rationalGapMatrix T v μ g) =
      star R * R + (2 * (g : ℝ) ^ 2) •
        rankOne ℝ (rationalUnitVector v) (rationalUnitVector v) - ((g : ℝ) ^ 2) • 1 := by
  simp only [rationalGapMatrix, map_sub, map_add, map_mul, rationalOperator_transpose,
    rationalOperator_smul, rationalReference_operator, rationalProjector_operator,
    map_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow]

theorem rationalGapMatrix_quadratic (T : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → ℚ) (μ g : ℚ) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x (rationalOperator (rationalGapMatrix T v μ g) x) =
      ‖residualReference (rationalOperator T) (rationalUnitVector v) μ x -
        (μ : ℝ) • x‖ ^ 2 + 2 * (g : ℝ) ^ 2 * |inner ℝ (rationalUnitVector v) x| ^ 2 -
        (g : ℝ) ^ 2 * ‖x‖ ^ 2 := by
  let R := residualReference (rationalOperator T) (rationalUnitVector v) (μ : ℝ) -
    (μ : ℝ) • 1
  have hn : inner ℝ x ((star R * R) x) = ‖R x‖ ^ 2 := by
    rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [rationalGapMatrix_operator]
  change inner ℝ x ((star R * R + _ - _) x) = _
  rw [_root_.sub_apply, _root_.add_apply, inner_sub_right, inner_add_right, hn]
  simp only [R, _root_.sub_apply, _root_.smul_apply,
    one_apply_eq_self, inner_smul_right, rankOne_apply, real_inner_self_eq_norm_sq,
    real_inner_comm x (rationalUnitVector v), sq_abs]
  ring

theorem rationalGapMatrix_certificate (T : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → ℚ) (μ g : ℚ)
    (hpsd : ((rationalGapMatrix T v μ g).map ((↑) : ℚ → ℝ)).PosSemidef) :
    ∀ x : EuclideanSpace ℝ (Fin n), (g : ℝ) ^ 2 * ‖x‖ ^ 2 ≤
      ‖residualReference (rationalOperator T) (rationalUnitVector v) μ x -
        (μ : ℝ) • x‖ ^ 2 + 2 * (g : ℝ) ^ 2 * |inner ℝ (rationalUnitVector v) x| ^ 2 := by
  intro x
  have hnonneg : 0 ≤ inner ℝ x (rationalOperator (rationalGapMatrix T v μ g) x) := by
    change 0 ≤ inner ℝ x ((rationalMatrixCast (rationalGapMatrix T v μ g)).toEuclideanLin x)
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, dotProduct_comm]
    exact hpsd.dotProduct_mulVec_nonneg _
  rw [rationalGapMatrix_quadratic] at hnonneg
  linarith

theorem rationalGapMatrix_certificate_iff (T : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → ℚ) (μ g : ℚ) :
    ((rationalGapMatrix T v μ g).map ((↑) : ℚ → ℝ)).PosSemidef ↔
    ∀ x : EuclideanSpace ℝ (Fin n), (g : ℝ) ^ 2 * ‖x‖ ^ 2 ≤
      ‖residualReference (rationalOperator T) (rationalUnitVector v) μ x -
        (μ : ℝ) • x‖ ^ 2 + 2 * (g : ℝ) ^ 2 * |inner ℝ (rationalUnitVector v) x| ^ 2 := by
  refine ⟨rationalGapMatrix_certificate T v μ g, fun h => ?_⟩
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    change rationalMatrixCast (rationalGapMatrix T v μ g).transpose =
      rationalMatrixCast (rationalGapMatrix T v μ g)
    rw [(rationalGapMatrix_isSymm T v μ g).eq]
  · intro y
    let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y
    have hn : 0 ≤ inner ℝ x (rationalOperator (rationalGapMatrix T v μ g) x) := by
      rw [rationalGapMatrix_quadratic]
      linarith [h x]
    change 0 ≤ inner ℝ x ((rationalMatrixCast (rationalGapMatrix T v μ g)).toEuclideanLin x) at hn
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, dotProduct_comm] at hn
    exact hn

/-- Every premise here is an exact finite rational check. Acceptance proves
an actual simple real eigenpair, with certified eigenvalue, direction, and
separation estimates. -/
theorem rationalResidual_certificate_sound (T : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → ℚ) (μ ε g : ℚ) (ldl : Maxwell.Certificate.LDLWitness n)
    (hT : T.IsSymm) (hv : v ≠ 0) (hε : 0 ≤ ε)
    (hres : rationalResidualSq T v μ ≤ ε ^ 2 * rationalNormSq v)
    (hldl : ldl.accepts (rationalGapMatrix T v μ g) = true) (hsmall : 4 * ε < g) :
    ∃ ν : ℝ, ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧
      rationalOperator T x = ν • x ∧ |ν - (μ : ℝ)| ≤ 2 * (ε : ℝ) ∧
      Module.finrank ℝ (eigenspace (rationalOperator T).toLinearMap ν) = 1 ∧
      0 < inner ℝ (rationalUnitVector v) x ∧
      ‖x - rationalUnitVector v‖ ≤ 8 * (ε : ℝ) / (g : ℝ) ∧
      ∀ (ρ : ℝ) (y : EuclideanSpace ℝ (Fin n)), ‖y‖ = 1 →
        rationalOperator T y = ρ • y → ν ≠ ρ → (g : ℝ) - 4 * (ε : ℝ) ≤ |ρ - ν| := by
  apply residual_quadratic_certificate_sound (rationalOperator T)
    (rationalOperator_symmetric T hT) (rationalUnitVector v) μ ε g
    (rationalUnitVector_norm v hv) (rationalResidual_bound T v μ ε hv hε hres)
    (rationalGapMatrix_certificate T v μ g (ldl.sound _ hldl))
  exact_mod_cast hsmall

/-- The same finite certificate applies to a real symmetric operator known
to lie within a certified operator-norm enclosure of the rational matrix. -/
theorem rationalResidual_approximation_sound (T : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → ℚ) (μ ε g : ℚ) (ldl : Maxwell.Certificate.LDLWitness n)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (σ : ℝ)
    (hT : T.IsSymm) (hv : v ≠ 0) (hε : 0 ≤ ε)
    (hres : rationalResidualSq T v μ ≤ ε ^ 2 * rationalNormSq v)
    (hldl : ldl.accepts (rationalGapMatrix T v μ g) = true)
    (hS : S.toLinearMap.IsSymmetric) (happrox : ‖S - rationalOperator T‖ ≤ σ)
    (hsmall : 2 * (σ + 2 * (ε : ℝ)) < (g : ℝ)) :
    ∃ ν : ℝ, ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧ S x = ν • x ∧
      |ν - (μ : ℝ)| ≤ σ + 2 * (ε : ℝ) ∧
      Module.finrank ℝ (eigenspace S.toLinearMap ν) = 1 ∧
      0 < inner ℝ (rationalUnitVector v) x ∧
      ‖x - rationalUnitVector v‖ ≤ 4 * (σ + 2 * (ε : ℝ)) / (g : ℝ) ∧
      ∀ (ρ : ℝ) (y : EuclideanSpace ℝ (Fin n)), ‖y‖ = 1 →
        S y = ρ • y → ν ≠ ρ → (g : ℝ) - 2 * (σ + 2 * (ε : ℝ)) ≤ |ρ - ν| := by
  let A := residualReference (rationalOperator T) (rationalUnitVector v) (μ : ℝ)
  have hu := rationalUnitVector_norm v hv
  have hr := rationalResidual_bound T v μ ε hv hε hres
  have hbound : ‖S - A‖ ≤ σ + 2 * (ε : ℝ) := by
    calc
      ‖S - A‖ ≤ ‖S - rationalOperator T‖ + ‖rationalOperator T - A‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (S - rationalOperator T) (rationalOperator T - A)
      _ ≤ σ + 2 * ‖rationalOperator T (rationalUnitVector v) -
          (μ : ℝ) • rationalUnitVector v‖ := add_le_add happrox
        (residualReference_norm _ (rationalOperator_symmetric T hT) _ _ hu)
      _ ≤ σ + 2 * (ε : ℝ) := by gcongr
  have hpert : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖S x - A x‖ ≤ (σ + 2 * (ε : ℝ)) * ‖x‖ := by
    intro x
    exact ((S - A).le_opNorm x).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))
  exact isolated_eigenpair_stability A.toLinearMap S.toLinearMap hS (rationalUnitVector v)
    μ (σ + 2 * (ε : ℝ)) g hu
    (residualReference_selected _ _ _ hu)
    (complementary_gap_of_quadratic_certificate A _ μ g
      (rationalGapMatrix_certificate T v μ g (ldl.sound _ hldl))) hpert hsmall

end Maxwell.Defect
