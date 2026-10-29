import Maxwell.Defect.RankOneBranch
import Maxwell.Defect.RankOneAsymptotics

/-! Transport from an arbitrary finite-dimensional symmetric reference
operator to its spectral coordinates, including the actual orthogonal
projection onto a possibly degenerate eigenspace. -/
namespace Maxwell.Defect

open Module.End
open InnerProductSpace

section Isometry
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

private theorem norm_isometry_conjugate_le (e : E ≃ₗᵢ[ℝ] F) (A : E →L[ℝ] E) :
    ‖e.conjStarAlgEquiv A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, e.norm_map, e.symm.norm_map]
    using A.le_opNorm (e.symm x)

theorem norm_isometry_conjugate (e : E ≃ₗᵢ[ℝ] F) (A : E →L[ℝ] E) :
    ‖e.conjStarAlgEquiv A‖ = ‖A‖ := by
  apply le_antisymm (norm_isometry_conjugate_le e A)
  have hh := norm_isometry_conjugate_le e.symm (e.conjStarAlgEquiv A)
  have he : e.symm.conjStarAlgEquiv (e.conjStarAlgEquiv A) = A := by ext x; simp
  simpa only [he] using hh

theorem isometry_conjugate_rankOne (e : E ≃ₗᵢ[ℝ] F) (w : E) :
    e.conjStarAlgEquiv (rankOne ℝ w w) = rankOne ℝ (e w) (e w) := by
  ext x
  have hi : inner ℝ w (e.symm x) = inner ℝ (e w) x := by
    simpa only [e.apply_symm_apply] using (e.inner_map_map w (e.symm x)).symm
  simp [rankOne_apply, hi]

/-- Orthogonal coordinates preserve the full eigenspace, not just individual
solutions of its eigenvector equation. -/
noncomputable def isometryConjugateEigenspaceEquiv (e : E ≃ₗᵢ[ℝ] F)
    (S : E →L[ℝ] E) (ν : ℝ) :
    eigenspace S.toLinearMap ν ≃ₗ[ℝ] eigenspace (e.conjStarAlgEquiv S).toLinearMap ν where
  toFun x := ⟨e x, by
    apply mem_eigenspace_iff.mpr
    change e (S (e.symm (e x))) = ν • e x
    have hx : S (x : E) = ν • (x : E) := mem_eigenspace_iff.mp x.property
    rw [e.symm_apply_apply, hx, map_smul]⟩
  invFun x := ⟨e.symm x, by
    apply mem_eigenspace_iff.mpr
    change S (e.symm x) = ν • e.symm x
    have hx := mem_eigenspace_iff.mp x.property
    change e (S (e.symm x)) = ν • (x : F) at hx
    have hh := congrArg e.symm hx
    simpa only [e.symm_apply_apply, map_smul] using hh⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_add' x y := Subtype.ext (map_add e (x : E) (y : E))
  map_smul' r x := Subtype.ext (map_smul e r (x : E))

end Isometry

section Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The mathematical orthogonal projection used in the rank-one lemma. -/
noncomputable def selectedProjection (A : E →L[ℝ] E) (lam : ℝ) (w : E) : E :=
  (eigenspace A.toLinearMap lam).starProjection w

/-- The spectral coordinate mask is exactly the orthogonal eigenspace
projection appearing in the statement of the paper's lemma. -/
theorem spectral_coordinates_projection (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (lam : ℝ) (w : E) :
    (hA.eigenvectorBasis rfl).repr (selectedProjection A lam w) =
      spectralP (hA.eigenvalues rfl) lam ((hA.eigenvectorBasis rfl).repr w) := by
  classical
  let b := hA.eigenvectorBasis rfl
  let d := hA.eigenvalues rfl
  let p := spectralP d lam (b.repr w)
  have hcoords (x : E) (i) : b.repr (A x) i = d i * b.repr x i :=
    hA.eigenvectorBasis_apply_self_apply rfl x i
  have hp : b.repr.symm p ∈ eigenspace A.toLinearMap lam := by
    apply mem_eigenspace_iff.mpr
    change A (b.repr.symm p) = lam • b.repr.symm p
    apply b.repr.injective
    ext i
    simp only [hcoords, b.repr.apply_symm_apply, map_smul, PiLp.smul_apply, smul_eq_mul]
    by_cases hi : d i = lam <;> simp [p, spectralP_apply, hi]
  have horth : ∀ z ∈ eigenspace A.toLinearMap lam,
      inner ℝ (w - b.repr.symm p) z = 0 := by
    intro z hz
    have heig : A z = lam • z := mem_eigenspace_iff.mp hz
    rw [← b.repr.inner_map_map]
    simp only [map_sub, b.repr.apply_symm_apply, EuclideanSpace.inner_eq_star_dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : d i = lam
    · simp [p, spectralP_apply, hi]
    · have he := congrArg (fun x : E => b.repr x i) heig
      simp only [hcoords, map_smul, PiLp.smul_apply, smul_eq_mul] at he
      have hzcoord : b.repr z i = 0 := by
        have hh : (d i - lam) * b.repr z i = 0 := by nlinarith
        exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hi)
      simp [hzcoord]
  have hp' : selectedProjection A lam w = b.repr.symm p :=
    Submodule.eq_starProjection_of_mem_of_inner_eq_zero hp horth
  change b.repr (selectedProjection A lam w) = p
  rw [hp', b.repr.apply_symm_apply]

/-- The actual symmetric reference becomes diagonal in the constructed
orthonormal eigenbasis. -/
theorem spectral_coordinates_operator (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) :
    (hA.eigenvectorBasis rfl).repr.conjStarAlgEquiv A =
      euclideanOperator (Matrix.diagonal (hA.eigenvalues rfl)) := by
  let b := hA.eigenvectorBasis rfl
  let d := hA.eigenvalues rfl
  have hcoords (x : E) (i) : b.repr (A x) i = d i * b.repr x i :=
    hA.eigenvectorBasis_apply_self_apply rfl x i
  ext x i
  change b.repr (A (b.repr.symm x)) i = ((Matrix.diagonal d).toEuclideanLin x) i
  rw [hcoords, b.repr.apply_symm_apply,
    diagonal_euclidean_apply]

theorem euclideanOperator_rankOne {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : EuclideanSpace ℝ ι) :
    euclideanOperator (Matrix.vecMulVec (WithLp.ofLp w) (WithLp.ofLp w)) = rankOne ℝ w w := by
  apply ContinuousLinearMap.ext
  intro x
  change (Matrix.vecMulVec (WithLp.ofLp w) (WithLp.ofLp w)).toEuclideanLin x =
    (inner ℝ w x) • w
  exact rankOneMatrix_apply w x

/-- Rank-one branch selection for an arbitrary finite-dimensional real
symmetric reference operator and the actual orthogonal eigenspace
projection. The hypotheses are exactly a nonzero projected perturbation
vector and a uniform quadratic operator remainder. -/
theorem rankOne_branch_selection
    (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (S : ℝ → E →L[ℝ] E) (w : E) (lam c C r : ℝ)
    (ha : selectedProjection A lam w ≠ 0) (hc : 0 < c) (hC : 0 ≤ C) (hr : 0 < r)
    (hS : ∀ τ, (S τ).toLinearMap.IsSymmetric)
    (hrem : ∀ τ, 0 < τ → τ < r →
      ‖S τ - A + (c * τ) • rankOne ℝ w w‖ ≤ C * τ ^ 2) :
    let a := selectedProjection A lam w
    ∃ η K L : ℝ, 0 < η ∧ 0 ≤ K ∧ 0 ≤ L ∧ ∀ τ : ℝ, 0 < τ → τ < η →
      ∃ ν : ℝ, ∃ u : E, ‖u‖ = 1 ∧ S τ u = ν • u ∧
        |ν - (lam - c * ‖a‖ ^ 2 * τ)| ≤ K * τ ^ 2 ∧
        Module.finrank ℝ (eigenspace (S τ).toLinearMap ν) = 1 ∧
        ‖u - ‖a‖⁻¹ • a‖ ≤ L * τ ∧
        |inner ℝ w u - ‖a‖| ≤ ‖w‖ * L * τ ∧ 0 < inner ℝ w u ∧
        ∀ (ρ : ℝ) (x : E), ‖x‖ = 1 → S τ x = ρ • x → ν ≠ ρ →
          c * ‖a‖ ^ 2 * τ / 2 ≤ |ρ - ν| := by
  classical
  let b := hA.eigenvectorBasis rfl
  let e := b.repr
  let d := hA.eigenvalues rfl
  let wc := e w
  let a := selectedProjection A lam w
  let Sc := fun τ => e.conjStarAlgEquiv (S τ)
  have hproj : e a = spectralP d lam wc := spectral_coordinates_projection A hA lam w
  have hpnorm : ‖spectralP d lam wc‖ = ‖a‖ := by rw [← hproj, e.norm_map]
  have hac : spectralP d lam wc ≠ 0 := by
    intro h
    apply ha
    change a = 0
    apply e.injective
    rw [hproj, map_zero]
    exact h
  have hAc : e.conjStarAlgEquiv A = euclideanOperator (Matrix.diagonal d) :=
    spectral_coordinates_operator A hA
  have hSc : ∀ τ, (Sc τ).toLinearMap.IsSymmetric := by
    intro τ
    apply IsSelfAdjoint.isSymmetric
    change star (e.conjStarAlgEquiv (S τ)) = e.conjStarAlgEquiv (S τ)
    rw [← map_star, (hS τ).isSelfAdjoint.star_eq]
  have hremc : ∀ τ, 0 < τ → τ < r →
      ‖Sc τ - euclideanOperator (Matrix.diagonal d) -
        τ • euclideanOperator (-c • Matrix.vecMulVec (WithLp.ofLp wc) (WithLp.ofLp wc))‖ ≤ C * τ ^ 2 := by
    intro τ hτ hτr
    have hid : Sc τ - euclideanOperator (Matrix.diagonal d) -
        τ • euclideanOperator (-c • Matrix.vecMulVec (WithLp.ofLp wc) (WithLp.ofLp wc)) =
        e.conjStarAlgEquiv (S τ - A + (c * τ) • rankOne ℝ w w) := by
      simp only [Sc, map_add, map_sub, map_smul, map_neg, hAc, isometry_conjugate_rankOne,
        euclideanOperator_rankOne, wc, neg_smul, smul_neg, smul_smul, sub_neg_eq_add]
      rw [mul_comm τ c]
    rw [hid, norm_isometry_conjugate]
    exact hrem τ hτ hτr
  obtain ⟨η, K, L, hη, hK, hL, hbranch⟩ :=
    rankOne_diagonal_branch_eventually d lam c C r wc Sc hac hc hC hr hSc hremc
  refine ⟨η, K, L, hη, hK, hL, ?_⟩
  intro τ hτ hτη
  obtain ⟨ν, u, hu, hSu, hν, hdim, halign, hinner, hpos, hsep⟩ := hbranch τ hτ hτη
  have hnorm : ‖e.symm u‖ = 1 := by rw [e.symm.norm_map, hu]
  have heigen : S τ (e.symm u) = ν • e.symm u := by
    have hh := congrArg e.symm hSu
    simpa only [Sc, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      e.symm_apply_apply, map_smul] using hh
  have hsimple : Module.finrank ℝ (eigenspace (S τ).toLinearMap ν) = 1 := by
    rw [(isometryConjugateEigenspaceEquiv e (S τ) ν).finrank_eq]
    exact hdim
  have hv : e.symm (‖spectralP d lam wc‖⁻¹ • spectralP d lam wc) = ‖a‖⁻¹ • a := by
    rw [← hproj, map_smul, e.symm_apply_apply, e.norm_map]
  have halign' : ‖e.symm u - ‖a‖⁻¹ • a‖ ≤ L * τ := by
    rw [← hv, ← map_sub, e.symm.norm_map]
    exact halign
  have hi : inner ℝ w (e.symm u) = inner ℝ wc u := by
    simpa only [wc, e.apply_symm_apply] using (e.inner_map_map w (e.symm u)).symm
  refine ⟨ν, e.symm u, hnorm, heigen, ?_, hsimple, halign', ?_, ?_, ?_⟩
  · simpa only [hpnorm] using hν
  · simpa only [hi, hpnorm, wc, e.norm_map] using hinner
  · rwa [hi]
  · intro ρ x hx hSx hne
    have hx' : ‖e x‖ = 1 := by rw [e.norm_map, hx]
    have he : Sc τ (e x) = ρ • e x := by
      simp only [Sc, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
        e.symm_apply_apply, hSx, map_smul]
    simpa only [hpnorm] using hsep ρ (e x) hx' he hne

end Spectral
end Maxwell.Defect
