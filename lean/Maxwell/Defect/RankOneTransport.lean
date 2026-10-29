import Maxwell.Defect.RankOneBlocks

/-! Transport between exact finite matrix blocks, Hilbert-space operator
norms, and the orthogonal Cayley coordinates. -/
namespace Maxwell.Defect

open Module.End

section MatrixTransport
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite real matrices acting on their Euclidean Hilbert space. The norm of
this operator is the Euclidean operator norm, rather than an entrywise norm. -/
noncomputable def euclideanOperator :
    Matrix ι ι ℝ ≃ₐ[ℝ] (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :=
  (Matrix.toLpLinAlgEquiv 2).trans (Module.End.toContinuousLinearMap _)

@[simp] theorem euclideanOperator_toLinearMap (M : Matrix ι ι ℝ) :
    (euclideanOperator M).toLinearMap = M.toEuclideanLin := rfl

@[simp] theorem euclideanOperator_transpose (M : Matrix ι ι ℝ) :
    euclideanOperator M.transpose = star (euclideanOperator M) := by
  change M.transpose.toEuclideanLin.toContinuousLinearMap =
    star M.toEuclideanLin.toContinuousLinearMap
  rw [ContinuousLinearMap.star_eq_adjoint, ← LinearMap.adjoint_toContinuousLinearMap]
  congr 1
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    M.toEuclideanLin_conjTranspose_eq_adjoint

/-- The exact matrix block generator is skew-adjoint as a Hilbert-space
operator, so its Cayley transform is orthogonal. -/
theorem euclidean_spectralBlockGenerator_skew (d : ι → ℝ) (lam : ℝ)
    (B : Matrix ι ι ℝ) (hB : B.IsSymm) :
    star (euclideanOperator (spectralBlockGenerator d lam B)) =
      -euclideanOperator (spectralBlockGenerator d lam B) := by
  rw [← euclideanOperator_transpose, spectralBlockGenerator_skew d lam B hB, map_neg]

/-- Exact first-order cancellation in the same operator algebra in which the
Cayley norm estimates are proved. -/
theorem euclidean_spectralBlockGenerator_cancel (d : ι → ℝ) (lam : ℝ)
    (B : Matrix ι ι ℝ) :
    euclideanOperator B +
      (euclideanOperator (Matrix.diagonal d) * euclideanOperator (spectralBlockGenerator d lam B) -
        euclideanOperator (spectralBlockGenerator d lam B) * euclideanOperator (Matrix.diagonal d)) =
      euclideanOperator (spectralBlockPart d lam B) := by
  simpa only [map_add, map_sub, map_mul] using
    congrArg euclideanOperator (spectralBlockGenerator_cancel d lam B)

end MatrixTransport

section UnitaryTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A unitary operator preserves vector norms exactly. -/
theorem unitary_operator_norm (U : E →L[ℝ] E) (hU : U ∈ unitary (E →L[ℝ] E)) (x : E) :
    ‖U x‖ = ‖x‖ := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self U).mpr
    (by simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using hU.1)

theorem unitary_star_apply_apply (U : E →L[ℝ] E) (hU : U ∈ unitary (E →L[ℝ] E)) (x : E) :
    star U (U x) = x := by
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using
    congrArg (fun T : E →L[ℝ] E => T x) hU.1

theorem unitary_apply_star_apply (U : E →L[ℝ] E) (hU : U ∈ unitary (E →L[ℝ] E)) (x : E) :
    U (star U x) = x := by
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using
    congrArg (fun T : E →L[ℝ] E => T x) hU.2

/-- Orthogonal conjugation transports the actual eigenvector equation. -/
theorem unitary_conjugate_eigenvector_iff (S U : E →L[ℝ] E)
    (hU : U ∈ unitary (E →L[ℝ] E)) (ν : ℝ) (u : E) :
    (star U * S * U) u = ν • u ↔ S (U u) = ν • U u := by
  constructor
  · intro h
    have hh := congrArg U h
    simpa only [mul_apply_eq_comp, unitary_apply_star_apply U hU, map_smul] using hh
  · intro h
    have hh := congrArg (fun x : E => (star U) x) h
    simpa only [mul_apply_eq_comp, unitary_star_apply_apply U hU, map_smul] using hh

/-- The entire eigenspace is preserved, including multiplicity. -/
noncomputable def unitaryConjugateEigenspaceEquiv (S U : E →L[ℝ] E)
    (hU : U ∈ unitary (E →L[ℝ] E)) (ν : ℝ) :
    eigenspace (star U * S * U).toLinearMap ν ≃ₗ[ℝ] eigenspace S.toLinearMap ν where
  toFun x := ⟨U x, mem_eigenspace_iff.mpr
    ((unitary_conjugate_eigenvector_iff S U hU ν x).mp (mem_eigenspace_iff.mp x.property))⟩
  invFun x := ⟨star U x, by
    apply mem_eigenspace_iff.mpr
    change (star U) (S (U (star U x))) = ν • star U x
    rw [unitary_apply_star_apply U hU]
    have hx : S (x : E) = ν • (x : E) := mem_eigenspace_iff.mp x.property
    rw [hx, map_smul]⟩
  left_inv x := Subtype.ext (unitary_star_apply_apply U hU x)
  right_inv x := Subtype.ext (unitary_apply_star_apply U hU x)
  map_add' x y := Subtype.ext (map_add U (x : E) (y : E))
  map_smul' r x := Subtype.ext (map_smul U r (x : E))

theorem unitary_conjugate_eigenspace_finrank (S U : E →L[ℝ] E)
    (hU : U ∈ unitary (E →L[ℝ] E)) (ν : ℝ) :
    Module.finrank ℝ (eigenspace (star U * S * U).toLinearMap ν) =
      Module.finrank ℝ (eigenspace S.toLinearMap ν) :=
  (unitaryConjugateEigenspaceEquiv S U hU ν).finrank_eq

/-- A near-identity orthogonal coordinate change only adds its own operator
distance from the identity to the normalized eigenvector error. -/
theorem unitary_eigenvector_distance (U : E →L[ℝ] E)
    (hU : U ∈ unitary (E →L[ℝ] E)) (u v : E) (hv : ‖v‖ = 1) :
    ‖U u - v‖ ≤ ‖u - v‖ + ‖U - 1‖ := by
  calc
    ‖U u - v‖ = ‖U (u - v) + (U v - v)‖ := by rw [map_sub]; congr 1; abel
    _ ≤ ‖U (u - v)‖ + ‖U v - v‖ := norm_add_le _ _
    _ = ‖u - v‖ + ‖(U - 1) v‖ := by rw [unitary_operator_norm U hU]; rfl
    _ ≤ ‖u - v‖ + ‖U - 1‖ * ‖v‖ := add_le_add (le_refl _) ((U - 1).le_opNorm v)
    _ = _ := by rw [hv, mul_one]

omit [CompleteSpace E] in
theorem inner_error_le (w u v : E) :
    |inner ℝ w u - inner ℝ w v| ≤ ‖w‖ * ‖u - v‖ := by
  rw [← inner_sub_right]
  exact abs_real_inner_le_norm w (u - v)

/-- The explicit constant from the proven Cayley conjugation bound. -/
noncomputable def cayleyErrorConstant (A B X : E →L[ℝ] E) (C : ℝ) : ℝ :=
  6 * (‖A‖ + ‖B‖ + C) * ‖X‖ ^ 2 + C + 2 * (‖B‖ + C) * ‖X‖

/-- Composition of actual Cayley block elimination, spectral perturbation,
and transport back to the original coordinates. -/
theorem cayley_selected_branch [FiniteDimensional ℝ E] [Nontrivial E]
    (A B D S X : E →L[ℝ] E) (τ C μ g : ℝ) (v : E)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hC : 0 ≤ C) (hXsmall : τ * ‖X‖ ≤ 1)
    (hX : star X = -X) (hS : S.toLinearMap.IsSymmetric)
    (hcancel : B + (A * X - X * A) = D)
    (hrem : ‖S - A - τ • B‖ ≤ C * τ ^ 2)
    (hv : ‖v‖ = 1) (hAv : (A + τ • D) v = μ • v)
    (hgap : ∀ y : E, inner ℝ v y = 0 → g * ‖y‖ ≤ ‖(A + τ • D) y - μ • y‖)
    (hsmall : 2 * (cayleyErrorConstant A B X C * τ ^ 2) < g) :
    ∃ ν : ℝ, ∃ u : E, ‖u‖ = 1 ∧ S u = ν • u ∧
      |ν - μ| ≤ cayleyErrorConstant A B X C * τ ^ 2 ∧
      Module.finrank ℝ (eigenspace S.toLinearMap ν) = 1 ∧
      ‖u - v‖ ≤ 4 * (cayleyErrorConstant A B X C * τ ^ 2) / g + 2 * τ * ‖X‖ ∧
      ∀ (ρ : ℝ) (x : E), ‖x‖ = 1 → S x = ρ • x → ν ≠ ρ →
        g - 2 * (cayleyErrorConstant A B X C * τ ^ 2) ≤ |ρ - ν| := by
  let U := cayley ((τ / 2) • X)
  let T := star U * S * U
  let R := A + τ • D
  let ε := cayleyErrorConstant A B X C * τ ^ 2
  obtain ⟨hU, hconj⟩ := cayley_first_order_conjugation A B S X τ C hτ hτ1 hC hXsmall hX hrem
  rw [hcancel] at hconj
  have hbound : ‖T - R‖ ≤ ε := by
    simpa only [T, U, R, ε, cayleyErrorConstant, sub_add_eq_sub_sub] using hconj
  have hpert : ∀ y : E, ‖T y - R y‖ ≤ ε * ‖y‖ := by
    intro y
    calc
      ‖T y - R y‖ = ‖(T - R) y‖ := rfl
      _ ≤ ‖T - R‖ * ‖y‖ := (T - R).le_opNorm y
      _ ≤ ε * ‖y‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
  have hT : T.toLinearMap.IsSymmetric := (hS.isSelfAdjoint.conjugate' U).isSymmetric
  obtain ⟨ν, u₀, hu₀, hTu₀, hν, hdim, _, halign, hsep⟩ :=
    isolated_eigenpair_stability R.toLinearMap T.toLinearMap hT v μ ε g hv hAv hgap hpert hsmall
  have hUdist : ‖U - 1‖ ≤ 2 * τ * ‖X‖ := by
    have hZnorm : ‖(τ / 2) • X‖ = (τ / 2) * ‖X‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ τ / 2 by positivity)]
    have hz : ‖(τ / 2) • X‖ ≤ 1 / 2 := by rw [hZnorm]; nlinarith
    have hh := cayley_sub_one_norm ((τ / 2) • X) hz
    rw [hZnorm] at hh
    dsimp [U]
    nlinarith
  have hnorm : ‖U u₀‖ = 1 := by rw [unitary_operator_norm U hU, hu₀]
  have heigen : S (U u₀) = ν • U u₀ :=
    (unitary_conjugate_eigenvector_iff S U hU ν u₀).mp hTu₀
  have hsimple : Module.finrank ℝ (eigenspace S.toLinearMap ν) = 1 := by
    rw [← unitary_conjugate_eigenspace_finrank S U hU ν]
    exact hdim
  refine ⟨ν, U u₀, hnorm, heigen, hν, hsimple, ?_, ?_⟩
  · exact (unitary_eigenvector_distance U hU u₀ v hv).trans (add_le_add halign hUdist)
  · intro ρ x hx hSx hne
    have hx' : ‖star U x‖ = 1 := by rw [unitary_operator_norm (star U) (Unitary.star_mem hU), hx]
    have he : T (star U x) = ρ • star U x := by
      change star U (S (U (star U x))) = ρ • star U x
      rw [unitary_apply_star_apply U hU, hSx, map_smul]
    exact hsep ρ (star U x) hx' he hne

end UnitaryTransport
end Maxwell.Defect
