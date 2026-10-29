import Maxwell.Certificate.Matrix
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! Complete finite rational certificates for nonnegative quadratic forms.
The existing exact checker permits arbitrary congruence factors; it need
not compute a pivoting or root-isolation algorithm. -/

namespace Maxwell.Defect

open Matrix LinearMap

/-- Every rational positive-semidefinite matrix has a finite accepted
congruence certificate. This is an existence/completeness theorem for the
executable rational checker, not an added oracle. -/
theorem exists_rational_psd_certificate {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : M.PosSemidef) :
    ∃ w : Certificate.LDLWitness n, w.accepts M = true := by
  have hsymm : LinearMap.IsSymm M.toBilin' := by
    constructor
    intro x y
    have htrans : M.transpose = M := by
      simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hM.isHermitian
    simp only [RingHom.id_apply, Matrix.toBilin'_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hij : M j i = M i j := congrFun (congrFun htrans i) j
    rw [hij]
    ring
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := M.toBilin') hsymm
  have hdim : Module.finrank ℚ (Fin n → ℚ) = n := by simp
  let b' : Module.Basis (Fin n) ℚ (Fin n → ℚ) := b.reindex (finCongr hdim)
  have hb' : LinearMap.IsOrthoᵢ M.toBilin' b' := by
    intro i j hij
    dsimp only [Function.onFun]
    simp only [b', Module.Basis.reindex_apply]
    apply hb
    exact fun h => hij ((finCongr hdim).symm.injective h)
  let diagonal : Fin n → ℚ := fun i => M.toBilin' (b' i) (b' i)
  have hdiag : BilinForm.toMatrix b' M.toBilin' = Matrix.diagonal diagonal := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [diagonal]
    · simp [BilinForm.toMatrix_apply, Matrix.diagonal, hij, hb' hij]
  have hpos : ∀ i, 0 ≤ diagonal i := by
    intro i
    simpa only [diagonal, Matrix.toBilin'_apply, dotProduct, Matrix.mulVec,
      Pi.star_apply, star_trivial, Finset.mul_sum, mul_assoc] using
      hM.dotProduct_mulVec_nonneg (b' i)
  let changeBasis := b'.toMatrix (Pi.basisFun ℚ (Fin n))
  have hmatrix : changeBasis.transpose * Matrix.diagonal diagonal * changeBasis = M := by
    have h := BilinForm.toMatrix_mul_basis_toMatrix b' (Pi.basisFun ℚ (Fin n)) M.toBilin'
    rw [hdiag, BilinForm.toMatrix_basisFun, BilinForm.toMatrix'_toBilin'] at h
    exact h
  refine ⟨⟨changeBasis.transpose, diagonal⟩, ?_⟩
  apply decide_eq_true
  exact ⟨by simpa using hmatrix.symm, hpos⟩

/-- Real positivity of a rational matrix is enough for the complete exact
checker. Restricting to rational vectors loses no soundness: the resulting
factorization is checked and reinterpreted over all real vectors. -/
theorem exists_rational_psd_certificate_of_real {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : (M.map ((↑) : ℚ → ℝ)).PosSemidef) :
    ∃ w : Certificate.LDLWitness n, w.accepts M = true := by
  apply exists_rational_psd_certificate
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    have h := congrFun (congrFun hM.isHermitian i) j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial] at h ⊢
    exact_mod_cast h
  · intro x
    have h := hM.dotProduct_mulVec_nonneg (fun i => (x i : ℝ))
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
      star_trivial] at h ⊢
    exact_mod_cast h

end Maxwell.Defect
