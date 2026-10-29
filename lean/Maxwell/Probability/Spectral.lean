import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

namespace Maxwell.Probability
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator


/-- Euclidean inverse bound, retaining invertibility explicitly so singular
matrices cannot pass through the totalized matrix inverse. -/
def InverseBound {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (L : ℝ) : Prop :=
  ∃ B : Matrix ι ι ℝ, A * B = 1 ∧ B * A = 1 ∧ ‖B‖ ≤ L

theorem inverseBound_norm_inv {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {L : ℝ}
    (h : InverseBound A L) : ‖A⁻¹‖ ≤ L := by
  obtain ⟨B, _, hBA, hnorm⟩ := h
  rw [Matrix.inv_eq_left_inv hBA]
  exact hnorm

/-- Spectral theorem for the shifted matrix, expressed in the original
orthonormal eigenbasis. -/
theorem shifted_spectral {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (σ : ℝ) :
    A - σ • (1 : Matrix ι ι ℝ) =
      Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => hA.eigenvalues i - σ)) := by
  rw [← Matrix.diagonal_sub]
  simp only [map_sub]
  congr 1
  · simpa using hA.spectral_theorem
  · have hdiag : Matrix.diagonal (fun _ : ι => σ) =
        σ • (1 : Matrix ι ι ℝ) := by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul]
      congr 1
      ext i
      simp
    rw [hdiag, map_smul, map_one]

/-- A gap in the complete finite spectrum yields the actual Euclidean
operator inverse bound. This includes both inverse identities. -/
theorem shifted_inverseBound {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (σ L : ℝ) (hL : 0 < L)
    (hgap : ∀ i, 1 / L ≤ |hA.eigenvalues i - σ|) :
    InverseBound (A - σ • (1 : Matrix ι ι ℝ)) L := by
  let φ := Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
  let dinv : ι → ℝ := fun i => (hA.eigenvalues i - σ)⁻¹
  have hne : ∀ i, hA.eigenvalues i - σ ≠ 0 := by
    intro i hi
    have hi' := hgap i
    rw [hi, abs_zero] at hi'
    exact (not_le_of_gt (one_div_pos.mpr hL)) hi'
  have hright : Matrix.diagonal (fun i => hA.eigenvalues i - σ) *
      Matrix.diagonal dinv = (1 : Matrix ι ι ℝ) := by
    rw [Matrix.diagonal_mul_diagonal]
    simpa only [dinv, mul_inv_cancel₀ (hne _)] using
      (Matrix.diagonal_one : Matrix.diagonal (fun _ : ι => (1 : ℝ)) = 1)
  have hleft : Matrix.diagonal dinv *
      Matrix.diagonal (fun i => hA.eigenvalues i - σ) = (1 : Matrix ι ι ℝ) := by
    rw [Matrix.diagonal_mul_diagonal]
    simpa only [dinv, inv_mul_cancel₀ (hne _)] using
      (Matrix.diagonal_one : Matrix.diagonal (fun _ : ι => (1 : ℝ)) = 1)
  refine ⟨φ (Matrix.diagonal dinv), ?_, ?_, ?_⟩
  · rw [shifted_spectral hA σ]
    change φ _ * φ _ = 1
    rw [← map_mul, hright, map_one]
  · rw [shifted_spectral hA σ]
    change φ _ * φ _ = 1
    rw [← map_mul, hleft, map_one]
  · dsimp [φ]
    simp only [← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hL.le).mpr
    intro i
    simp only [dinv, Real.norm_eq_abs, abs_inv]
    exact (inv_le_comm₀ (abs_pos.mpr (hne i)) hL).mpr (by simpa using hgap i)

end
end Maxwell.Probability
