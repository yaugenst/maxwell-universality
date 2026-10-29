import Maxwell.Spectral.ConcreteFolding
import Maxwell.Spectral.SimpleSplitting

/-!
# Simplicity under the actual unitary sector folding

A simple eigenvector in one block lifts to a simple eigenvector of the full
matrix when the other blocks exclude that energy. The other-sector exclusion
is explicit; it is not inferred from primitive simplicity alone.
-/
namespace Maxwell.Spectral.SectorSimplicity

noncomputable section
open scoped Matrix

variable {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ]
  [DecidableEq α] [DecidableEq ι] [DecidableEq κ]

def sectorEmbedding (a : α) (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ (ι × α) :=
  WithLp.toLp 2 fun p => if p.2 = a then v p.1 else 0

def sectorComponent (a : α) (x : EuclideanSpace ℂ (ι × α)) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun i => x (i, a)

omit [DecidableEq ι] in
theorem sectorDiagonal_mulVec (B : α → Matrix ι ι ℂ) (x : (ι × α) → ℂ)
    (i : ι) (a : α) :
    (sectorDiagonal B).mulVec x (i, a) = (B a).mulVec (fun j => x (j, a)) i := by
  simp [Matrix.mulVec, dotProduct, sectorDiagonal, Fintype.sum_prod_type, ite_mul]

theorem sectorComponent_eigenvector (B : α → Matrix ι ι ℂ)
    (E : ℂ) (x : EuclideanSpace ℂ (ι × α))
    (hx : (sectorDiagonal B).toEuclideanLin x = E • x) (a : α) :
    (B a).toEuclideanLin (sectorComponent a x) = E • sectorComponent a x := by
  ext i
  have hi := congrArg (fun y : EuclideanSpace ℂ (ι × α) => y (i, a)) hx
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
    sectorDiagonal_mulVec, PiLp.smul_apply, smul_eq_mul, sectorComponent] using hi

theorem sectorEmbedding_eigenvector (B : α → Matrix ι ι ℂ) (a : α)
    (E : ℂ) (v : EuclideanSpace ℂ ι) (hv : (B a).toEuclideanLin v = E • v) :
    (sectorDiagonal B).toEuclideanLin (sectorEmbedding a v) = E • sectorEmbedding a v := by
  ext ⟨i, b⟩
  change (sectorDiagonal B).mulVec (fun p => if p.2 = a then v p.1 else 0) (i, b) = _
  rw [sectorDiagonal_mulVec]
  by_cases h : b = a
  · subst b
    have hi := congrArg (fun y : EuclideanSpace ℂ ι => y i) hv
    simpa [sectorEmbedding, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using hi
  · simp [h, sectorEmbedding, Matrix.mulVec, dotProduct]

/-- No eigenvector can have a component in an excluded sector. -/
theorem sectorDiagonal_eigenvectors_span (B : α → Matrix ι ι ℂ) (a : α)
    (E : ℂ) (v : EuclideanSpace ℂ ι)
    (hsimple : ∀ x : EuclideanSpace ℂ ι,
      (B a).toEuclideanLin x = E • x → ∃ c : ℂ, x = c • v)
    (hexclude : ∀ b : α, b ≠ a → ∀ x : EuclideanSpace ℂ ι,
      (B b).toEuclideanLin x = E • x → x = 0)
    (x : EuclideanSpace ℂ (ι × α)) (hx : (sectorDiagonal B).toEuclideanLin x = E • x) :
    ∃ c : ℂ, x = c • sectorEmbedding a v := by
  obtain ⟨c, hc⟩ := hsimple (sectorComponent a x) (sectorComponent_eigenvector B E x hx a)
  refine ⟨c, ?_⟩
  ext ⟨i, b⟩
  by_cases h : b = a
  · subst b
    have hi := congrArg (fun y : EuclideanSpace ℂ ι => y i) hc
    simpa [sectorComponent, sectorEmbedding] using hi
  · have hb := hexclude b h (sectorComponent b x) (sectorComponent_eigenvector B E x hx b)
    have hi := congrArg (fun y : EuclideanSpace ℂ ι => y i) hb
    simpa [sectorComponent, sectorEmbedding, h] using hi

omit [DecidableEq ι] in
theorem sectorEmbedding_norm (a : α) (v : EuclideanSpace ℂ ι) :
    ‖sectorEmbedding a v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, sectorEmbedding, Fintype.sum_prod_type, apply_ite]

/-- A rectangular two-sided unitary gives the actual Hilbert-space
identification, including different finite index types. -/
def matrixUnitaryEquiv (U : Matrix κ ι ℂ)
    (hleft : U.conjTranspose * U = 1) (hright : U * U.conjTranspose = 1) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ :=
  LinearEquiv.isometryOfInner
    { toLinearMap := U.toEuclideanLin
      invFun := U.conjTranspose.toEuclideanLin
      left_inv := by
        intro x
        change U.conjTranspose.toEuclideanLin (U.toEuclideanLin x) = x
        have he := congrArg (fun M : Matrix ι ι ℂ => M.toEuclideanLin x) hleft
        simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
          LinearMap.comp_apply, Matrix.toLpLin_one, LinearMap.id_apply] using he
      right_inv := by
        intro y
        change U.toEuclideanLin (U.conjTranspose.toEuclideanLin y) = y
        have he := congrArg (fun M : Matrix κ κ ℂ => M.toEuclideanLin y) hright
        simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
          LinearMap.comp_apply, Matrix.toLpLin_one, LinearMap.id_apply] using he }
    (by
      intro x y
      change inner ℂ (U.toEuclideanLin x) (U.toEuclideanLin y) = inner ℂ x y
      rw [← LinearMap.adjoint_inner_right]
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      have he := congrArg (fun M : Matrix ι ι ℂ => M.toEuclideanLin y) hleft
      have hy : U.conjTranspose.toEuclideanLin (U.toEuclideanLin y) = y := by
        simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
          LinearMap.comp_apply, Matrix.toLpLin_one, LinearMap.id_apply] using he
      rw [hy])

/-- The normalized conventional vector with the exact folding gauge. -/
def liftedVector (U : Matrix κ (ι × α) ℂ) (a : α) (v : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ κ := U.toEuclideanLin (sectorEmbedding a v)

theorem unitary_sector_simplicity (A : Matrix κ κ ℂ)
    (B : α → Matrix ι ι ℂ) (U : Matrix κ (ι × α) ℂ)
    (hleft : U.conjTranspose * U = 1) (hright : U * U.conjTranspose = 1)
    (hinter : A * U = U * sectorDiagonal B) (a : α) (E : ℂ)
    (v : EuclideanSpace ℂ ι) (hvnorm : ‖v‖ = 1)
    (hv : (B a).toEuclideanLin v = E • v)
    (hsimple : ∀ x : EuclideanSpace ℂ ι,
      (B a).toEuclideanLin x = E • x → ∃ c : ℂ, x = c • v)
    (hexclude : ∀ b : α, b ≠ a → ∀ x : EuclideanSpace ℂ ι,
      (B b).toEuclideanLin x = E • x → x = 0) :
    ‖liftedVector U a v‖ = 1 ∧
      A.toEuclideanLin (liftedVector U a v) = E • liftedVector U a v ∧
      Module.finrank ℂ (Module.End.eigenspace A.toEuclideanLin E) = 1 := by
  let e := matrixUnitaryEquiv U hleft hright
  have he (x : EuclideanSpace ℂ (ι × α)) :
      A.toEuclideanLin (e x) = e ((sectorDiagonal B).toEuclideanLin x) := by
    change A.toEuclideanLin (U.toEuclideanLin x) =
      U.toEuclideanLin ((sectorDiagonal B).toEuclideanLin x)
    have hh := congrArg (fun M : Matrix κ (ι × α) ℂ => M.toEuclideanLin x) hinter
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply] using hh
  have hnorm : ‖liftedVector U a v‖ = 1 := by
    change ‖e (sectorEmbedding a v)‖ = 1
    rw [e.norm_map, sectorEmbedding_norm, hvnorm]
  have hveig : A.toEuclideanLin (liftedVector U a v) = E • liftedVector U a v := by
    change A.toEuclideanLin (e (sectorEmbedding a v)) = E • e (sectorEmbedding a v)
    rw [he, sectorEmbedding_eigenvector B a E v hv, e.map_smul]
  have hall (x : EuclideanSpace ℂ κ) (hx : A.toEuclideanLin x = E • x) :
      ∃ c : ℂ, x = c • liftedVector U a v := by
    have hx' : (sectorDiagonal B).toEuclideanLin (e.symm x) = E • e.symm x := by
      apply e.injective
      rw [← he, e.apply_symm_apply, e.map_smul, e.apply_symm_apply, hx]
    obtain ⟨c, hc⟩ := sectorDiagonal_eigenvectors_span B a E v hsimple hexclude (e.symm x) hx'
    refine ⟨c, ?_⟩
    have hh := congrArg e hc
    change x = c • e (sectorEmbedding a v)
    simpa only [e.apply_symm_apply, e.map_smul] using hh
  have hspace : Module.End.eigenspace A.toEuclideanLin E =
      Submodule.span ℂ {liftedVector U a v} := by
    ext x
    rw [Module.End.mem_eigenspace_iff, Submodule.mem_span_singleton]
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := hall x hx
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, rfl⟩
      rw [map_smul, hveig]
      module
  refine ⟨hnorm, hveig, ?_⟩
  rw [hspace]
  apply finrank_span_singleton
  intro hz
  rw [hz, norm_zero] at hnorm
  exact zero_ne_one hnorm

section Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- Indexed simplicity in a finite Hermitian sector gives its exact
one-dimensional eigenspace, with the chosen normalized eigenvector. -/
theorem simple_eigenvectors_span (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℂ H))
    (hsimple : ∀ j, j ≠ i → hT.eigenvalues rfl j ≠ hT.eigenvalues rfl i)
    (x : H) (hx : T x = (hT.eigenvalues rfl i : ℂ) • x) :
    ∃ c : ℂ, x = c • hT.eigenvectorBasis rfl i := by
  let u := hT.eigenvectorBasis rfl i
  let c := inner ℂ u x
  have hu : T u = (hT.eigenvalues rfl i : ℂ) • u := by
    simpa only [u, RCLike.ofReal_eq_complex_ofReal] using hT.apply_eigenvectorBasis rfl i
  have hz : x - c • u = 0 := by
    apply SimpleSplitting.simple_complement_kernel T hT i hsimple
    · change inner ℂ u (x - c • u) = 0
      rw [inner_sub_right, inner_smul_right]
      have hn : inner ℂ u u = 1 := (hT.eigenvectorBasis rfl).inner_eq_one i
      rw [hn, mul_one]
      exact sub_self c
    · rw [map_sub, map_smul, hx, hu]
      module
  exact ⟨c, sub_eq_zero.mp hz⟩

/-- Excluding a real energy from every eigenvalue excludes every nonzero
eigenvector at that energy. -/
theorem excluded_eigenvalue_kernel (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (E : ℝ) (hexclude : ∀ j, hT.eigenvalues rfl j ≠ E)
    (x : H) (hx : T x = (E : ℂ) • x) : x = 0 := by
  let b := hT.eigenvectorBasis rfl
  apply b.repr.injective
  ext j
  simp only [map_zero, PiLp.zero_apply]
  have he := congrArg (fun y : H => b.repr y j) hx
  simp only [b, hT.eigenvectorBasis_apply_self_apply, map_smul,
    PiLp.smul_apply, smul_eq_mul, RCLike.ofReal_eq_complex_ofReal] at he
  have hne : (hT.eigenvalues rfl j : ℂ) ≠ (E : ℂ) := by exact_mod_cast hexclude j
  have hz : ((hT.eigenvalues rfl j : ℂ) - (E : ℂ)) * b.repr x j = 0 := by
    change ((_ : ℂ) - _) * (hT.eigenvectorBasis rfl).repr x j = 0
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

/-- A one-dimensional actual eigenspace determines a unique entry in the
ordered spectral list. -/
theorem unique_eigenvalue_index_of_finrank_one (T : H →ₗ[ℂ] H) (hT : T.IsSymmetric)
    (E : ℝ) (hdim : Module.finrank ℂ (Module.End.eigenspace T (E : ℂ)) = 1) :
    ∃ i : Fin (Module.finrank ℂ H), hT.eigenvalues rfl i = E ∧
      ∀ j, j ≠ i → hT.eigenvalues rfl j ≠ hT.eigenvalues rfl i := by
  classical
  have hc : (Finset.univ.filter fun i => hT.eigenvalues rfl i = E).card = 1 := by
    have h := hT.card_filter_eigenvalues_eq rfl (E : ℂ)
    simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_inj, hdim] using h
  obtain ⟨i, hi, huniq⟩ := Finset.card_eq_one_iff_existsUnique.mp hc
  have hiE := (Finset.mem_filter.mp hi).2
  refine ⟨i, hiE, ?_⟩
  intro j hji hj
  have hjE : hT.eigenvalues rfl j = E := hj.trans hiE
  exact hji (huniq j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjE⟩))

end Spectral

open Maxwell.Spectral.PeriodicYee

theorem primitive_symmetric (k : Momentum) (a : Folding.Coset) :
    (PrimitiveYee.fiber Concrete.material (Folding.sectorMomentum k a)).toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (PrimitiveYee.fiber_hermitian _ _)

theorem conventional_symmetric (k : Momentum) :
    (PeriodicYee.fiber Concrete.material (Folding.conventionalMomentum k)).toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (PeriodicYee.fiber_hermitian _ _)

/-- Primitive simplicity and exclusion from the other three actual primitive
sectors imply simplicity of the frozen conventional 24000-dimensional fiber.
The vector uses the exact normalized Bloch folding gauge. -/
theorem concrete_folding_simple (k : Momentum) (a : Folding.Coset)
    (i : Fin (Module.finrank ℂ (EuclideanSpace ℂ PrimitiveYee.Electric)))
    (hsimple : ∀ j, j ≠ i → (primitive_symmetric k a).eigenvalues rfl j ≠
      (primitive_symmetric k a).eigenvalues rfl i)
    (hexclude : ∀ b : Folding.Coset, b ≠ a → ∀ j,
      (primitive_symmetric k b).eigenvalues rfl j ≠
        (primitive_symmetric k a).eigenvalues rfl i) :
    let E := (primitive_symmetric k a).eigenvalues rfl i
    let φ := liftedVector (Folding.foldingMatrix k) a
      ((primitive_symmetric k a).eigenvectorBasis rfl i)
    ‖φ‖ = 1 ∧
      (PeriodicYee.fiber Concrete.material (Folding.conventionalMomentum k)).toEuclideanLin φ =
        (E : ℂ) • φ ∧
      Module.finrank ℂ (Module.End.eigenspace
        (PeriodicYee.fiber Concrete.material (Folding.conventionalMomentum k)).toEuclideanLin
          (E : ℂ)) = 1 ∧
      ∃ j : Fin (Module.finrank ℂ (EuclideanSpace ℂ Electric20)),
        (conventional_symmetric k).eigenvalues rfl j = E ∧
        ∀ l, l ≠ j → (conventional_symmetric k).eigenvalues rfl l ≠
          (conventional_symmetric k).eigenvalues rfl j := by
  dsimp only
  obtain ⟨hn, he, hd⟩ := unitary_sector_simplicity
    (PeriodicYee.fiber Concrete.material (Folding.conventionalMomentum k))
    (fun b => PrimitiveYee.fiber Concrete.material (Folding.sectorMomentum k b))
    (Folding.foldingMatrix k) (Concrete.primitive_folding_unitary k).1
    (Concrete.primitive_folding_unitary k).2 (Concrete.primitive_folding_intertwining k)
    a ((primitive_symmetric k a).eigenvalues rfl i : ℂ)
    ((primitive_symmetric k a).eigenvectorBasis rfl i)
    (((primitive_symmetric k a).eigenvectorBasis rfl).norm_eq_one i)
    (by simpa only [RCLike.ofReal_eq_complex_ofReal] using
      (primitive_symmetric k a).apply_eigenvectorBasis rfl i)
    (simple_eigenvectors_span _ (primitive_symmetric k a) i hsimple)
    (fun b hb => excluded_eigenvalue_kernel _ (primitive_symmetric k b)
      ((primitive_symmetric k a).eigenvalues rfl i) (hexclude b hb))
  exact ⟨hn, he, hd, unique_eigenvalue_index_of_finrank_one _ (conventional_symmetric k)
    ((primitive_symmetric k a).eigenvalues rfl i) hd⟩

end
end Maxwell.Spectral.SectorSimplicity
