import Maxwell.Spectral.InertiaCongruence
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Invertible
import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Signed LDL factorizations imply actual spectral inertia

The input is an exact complex factorization with real pivots and an invertible
factor. Triangularity is unnecessary for the semantic theorem; a finite checker
may establish invertibility from its own triangular contract. No numerical
spectral assertion is an input.
-/

namespace Maxwell.Spectral.LDLInertia

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual real-pivot diagonal form in the standard orthonormal basis. -/
theorem real_diagonal_quadratic_form (d : n → ℝ) (x : EuclideanSpace ℂ n) :
    Complex.re (inner ℂ x ((Matrix.diagonal (fun i => (d i : ℂ))).toEuclideanLin x)) =
      ∑ i, d i * ‖(EuclideanSpace.basisFun n ℂ).repr x i‖ ^ 2 := by
  apply diagonal_quadratic_form (EuclideanSpace.basisFun n ℂ) d
  intro y i
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_diagonal,
    EuclideanSpace.basisFun_repr]

/-- The invertible change of coordinates in `M = L D Lᴴ` is `Lᴴ`. -/
def coordinateEquiv (L : Matrix n n ℂ) (hL : IsUnit L) :
    EuclideanSpace ℂ n ≃ₗ[ℂ] EuclideanSpace ℂ n :=
  LinearEquiv.ofBijective L.conjTranspose.toEuclideanLin
    ((Module.End.isUnit_iff _).mp
      (((Matrix.isUnit_conjTranspose L).mpr hL).map (Matrix.toLpLinAlgEquiv (R := ℂ) 2)))

/-- Exact LDL equality gives equality of the real quadratic forms after the
invertible coordinate change. -/
theorem factorization_quadratic_congruence (M L : Matrix n n ℂ) (d : n → ℝ)
    (hL : IsUnit L)
    (hfactor : M = L * Matrix.diagonal (fun i => (d i : ℂ)) * L.conjTranspose)
    (x : EuclideanSpace ℂ n) :
    Complex.re (inner ℂ (coordinateEquiv L hL x)
      ((Matrix.diagonal (fun i => (d i : ℂ))).toEuclideanLin (coordinateEquiv L hL x))) =
      Complex.re (inner ℂ x (M.toEuclideanLin x)) := by
  change Complex.re (inner ℂ (L.conjTranspose.toEuclideanLin x)
    ((Matrix.diagonal (fun i => (d i : ℂ))).toEuclideanLin
      (L.conjTranspose.toEuclideanLin x))) = _
  rw [hfactor]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  rw [show Matrix.toLpLin 2 2 L.conjTranspose =
      L.toEuclideanLin.adjoint from Matrix.toEuclideanLin_conjTranspose_eq_adjoint L]
  rw [LinearMap.adjoint_inner_left]

/-- A real-pivot exact factorization is Hermitian, regardless of pivot signs. -/
theorem factorization_isHermitian (M L : Matrix n n ℂ) (d : n → ℝ)
    (hfactor : M = L * Matrix.diagonal (fun i => (d i : ℂ)) * L.conjTranspose) :
    M.IsHermitian := by
  rw [hfactor]
  have hd : (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star (d i : ℂ) = (d i : ℂ)
    simp
  exact Matrix.isHermitian_mul_mul_conjTranspose L hd

/-- Kernel-checked LDL semantics: actual selfadjoint eigenvalue multiplicities
are exactly the negative, zero, and positive pivot counts. The caller's
symmetry proof can be obtained from `factorization_isHermitian`. -/
theorem eigenvalue_inertia (M L : Matrix n n ℂ) (d : n → ℝ)
    (hM : M.toEuclideanLin.IsSymmetric) (hL : IsUnit L)
    (hfactor : M = L * Matrix.diagonal (fun i => (d i : ℂ)) * L.conjTranspose) :
    (Finset.univ.filter fun i => hM.eigenvalues rfl i < 0).card =
      (Finset.univ.filter fun i => d i < 0).card ∧
    (Finset.univ.filter fun i => hM.eigenvalues rfl i = 0).card =
      (Finset.univ.filter fun i => d i = 0).card ∧
    (Finset.univ.filter fun i => 0 < hM.eigenvalues rfl i).card =
      (Finset.univ.filter fun i => 0 < d i).card := by
  exact ⟨card_negative_eq_of_diagonal_congruence M.toEuclideanLin
      (Matrix.diagonal (fun i => (d i : ℂ))).toEuclideanLin
      (hM.eigenvectorBasis rfl) (EuclideanSpace.basisFun n ℂ)
      (hM.eigenvalues rfl) d (spectral_quadratic_form hM)
      (real_diagonal_quadratic_form d) (coordinateEquiv L hL)
      (factorization_quadratic_congruence M L d hL hfactor),
    card_zero_eq_of_diagonal_congruence M.toEuclideanLin
      (Matrix.diagonal (fun i => (d i : ℂ))).toEuclideanLin
      (hM.eigenvectorBasis rfl) (EuclideanSpace.basisFun n ℂ)
      (hM.eigenvalues rfl) d (spectral_quadratic_form hM)
      (real_diagonal_quadratic_form d) (coordinateEquiv L hL)
      (factorization_quadratic_congruence M L d hL hfactor),
    card_positive_eq_of_diagonal_congruence M.toEuclideanLin
      (Matrix.diagonal (fun i => (d i : ℂ))).toEuclideanLin
      (hM.eigenvectorBasis rfl) (EuclideanSpace.basisFun n ℂ)
      (hM.eigenvalues rfl) d (spectral_quadratic_form hM)
      (real_diagonal_quadratic_form d) (coordinateEquiv L hL)
      (factorization_quadratic_congruence M L d hL hfactor)⟩

/-- Exact rational factorization equality transports to the complex operator
without rounding or a numerical matrix reconstruction. -/
theorem rational_factorization_complex (M L : Matrix n n ℚ) (d : n → ℚ)
    (hfactor : M = L * Matrix.diagonal d * L.transpose) :
    M.map ((↑) : ℚ → ℂ) = L.map ((↑) : ℚ → ℂ) *
      Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) *
        (L.map ((↑) : ℚ → ℂ)).conjTranspose := by
  rw [hfactor, Matrix.map_mul_ratCast, Matrix.map_mul_ratCast]
  have hd : (Matrix.diagonal d).map ((↑) : ℚ → ℂ) =
      Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_map (by simp)]
    simp
  have ht : L.transpose.map ((↑) : ℚ → ℂ) =
      (L.map ((↑) : ℚ → ℂ)).conjTranspose := by
    ext i j
    simp
  rw [hd, ht]

/-- The rational finite-checker interface: exact equality and invertibility
give actual complex spectral inertia, with pivot signs checked over `ℚ`. -/
theorem rational_eigenvalue_inertia (M L : Matrix n n ℚ) (d : n → ℚ)
    (hM : (M.map ((↑) : ℚ → ℂ)).toEuclideanLin.IsSymmetric)
    (hL : IsUnit L) (hfactor : M = L * Matrix.diagonal d * L.transpose) :
    (Finset.univ.filter fun i => hM.eigenvalues rfl i < 0).card =
      (Finset.univ.filter fun i => d i < 0).card ∧
    (Finset.univ.filter fun i => hM.eigenvalues rfl i = 0).card =
      (Finset.univ.filter fun i => d i = 0).card ∧
    (Finset.univ.filter fun i => 0 < hM.eigenvalues rfl i).card =
      (Finset.univ.filter fun i => 0 < d i).card := by
  have hu : IsUnit (L.map ((↑) : ℚ → ℂ)) :=
    hL.map (Rat.castHom ℂ).mapMatrix
  simpa only [Rat.cast_lt_zero, Rat.cast_eq_zero, Rat.cast_pos] using
    eigenvalue_inertia (M.map ((↑) : ℚ → ℂ)) (L.map ((↑) : ℚ → ℂ))
      (fun i => (d i : ℝ)) hM hu (rational_factorization_complex M L d hfactor)

end
end Maxwell.Spectral.LDLInertia
