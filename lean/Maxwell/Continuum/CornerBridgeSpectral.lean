import Maxwell.Continuum.CornerBridgeCoordinates
import Mathlib.Analysis.Matrix.Spectrum

/-! Real Rayleigh bounds for the literal certified corner matrices. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CornerBridge

open scoped InnerProductSpace

/-- A root bound gives a quadratic-form bound for a real symmetric matrix. -/
theorem real_matrix_rayleigh_le (M : Corner.Mat) (hM : M.transpose = M) (c : ℝ)
    (hc : ∀ x : ℝ, M.charpoly.IsRoot x → x ≤ c) (v : Corner.Vec) :
    dotProduct v (M.mulVec v) ≤ c * dotProduct v v := by
  have hherm : M.IsHermitian := by
    have he : M.conjTranspose = M.transpose := by ext i j; simp
    exact he.trans hM
  let T := M.toEuclideanLin
  have hs : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hherm
  let b := hs.eigenvectorBasis (show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by simp)
  let x : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 v
  have hroot (j : Fin 3) : M.charpoly.IsRoot (hs.eigenvalues (by simp) j) := by
    have hh := (Module.End.hasEigenvalue_iff_isRoot_charpoly T _).mp
      (hs.hasEigenvalue_eigenvalues (by simp) j)
    simpa only [T,Matrix.toEuclideanLin_eq_toLin_orthonormal,Matrix.charpoly_toLin,RCLike.ofReal_real_eq_id,id_eq] using hh
  have hform : inner ℝ x (T x) =
      ∑ j : Fin 3, hs.eigenvalues (by simp) j * (b.repr x j)^2 := by
    rw [← b.repr.inner_map_map x (T x),PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hs.eigenvectorBasis_apply_self_apply]
    simp only [RCLike.inner_apply,RCLike.conj_to_real,RCLike.ofReal_real_eq_id,id_eq]
    ring
  have hnorm : inner ℝ x x = ∑ j : Fin 3, (b.repr x j)^2 := by
    rw [← b.repr.inner_map_map x x,PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [RCLike.inner_apply,RCLike.conj_to_real,pow_two]
  have h : inner ℝ x (T x) ≤ c * inner ℝ x x := by
    rw [hform,hnorm,Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hc _ (hroot j)) (sq_nonneg _))
  simpa only [x,T,Matrix.toLpLin_apply,PiLp.inner_apply,RCLike.inner_apply,
    RCLike.conj_to_real,dotProduct,mul_comm] using h

theorem other_parity_rayleigh (p : Corner.Parity) (hp : p ≠ Corner.selectedParity) (v : Corner.Vec) :
    dotProduct v ((Corner.parityBlock p).mulVec v) ≤ Corner.lambdaNext * dotProduct v v := by
  apply real_matrix_rayleigh_le _ (Corner.block_transpose _)
  intro x hx
  rcases (Corner.parity_charpoly_roots p x).mp hx with rfl | rfl | rfl
  · unfold Corner.lambdaNext
    positivity
  · exact Corner.other_root_le_next p true (by simpa using hp)
  · exact Corner.other_root_le_next p false (by simp)

end Maxwell.Continuum.CornerBridge
