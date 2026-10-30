import Maxwell.Continuum.CalibrationRationalMatrix
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Executable rational symmetrization preserves the approximation error
to an actual symmetric operator in the orthonormal 24-coordinate space. -/

namespace Maxwell.Continuum.Calibration

noncomputable section

theorem centralMatrixCLM_conjTranspose (M : Matrix (Fin 24) (Fin 24) ℂ) :
    centralMatrixCLM M.conjTranspose = (centralMatrixCLM M).adjoint := by
  unfold centralMatrixCLM
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_conjTranspose,
    LinearMap.adjoint_toContinuousLinearMap]

theorem centralMatrixCLM_add (M N : Matrix (Fin 24) (Fin 24) ℂ) :
    centralMatrixCLM (M+N) = centralMatrixCLM M+centralMatrixCLM N := by
  apply ContinuousLinearMap.coe_injective
  exact map_add Matrix.toEuclideanLin M N

theorem centralMatrixCLM_smul (c : ℂ) (M : Matrix (Fin 24) (Fin 24) ℂ) :
    centralMatrixCLM (c • M) = c • centralMatrixCLM M := by
  apply ContinuousLinearMap.coe_injective
  exact map_smul Matrix.toEuclideanLin c M

end

def symmetricRationalMatrix (M : Matrix (Fin 24) (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℚ :=
  (1/2 : ℚ) • (M+M.transpose)

theorem symmetricRationalMatrix_transpose (M : Matrix (Fin 24) (Fin 24) ℚ) :
    (symmetricRationalMatrix M).transpose = symmetricRationalMatrix M := by
  ext i j
  change (1/2 : ℚ)*(M j i+M i j) = (1/2 : ℚ)*(M i j+M j i)
  ring

theorem symmetricRationalMatrix_cast (M : Matrix (Fin 24) (Fin 24) ℚ) :
    (symmetricRationalMatrix M).map (Rat.castHom ℂ) =
      (1/2 : ℂ) • (M.map (Rat.castHom ℂ)+(M.map (Rat.castHom ℂ)).conjTranspose) := by
  ext i j
  change (((1/2 : ℚ)*(M i j+M j i) : ℚ) : ℂ) =
    (1/2 : ℂ)*((M i j : ℂ)+star (M j i : ℂ))
  simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_add, star_ratCast]

theorem symmetricRationalMatrix_operator (M : Matrix (Fin 24) (Fin 24) ℚ) :
    centralMatrixCLM ((symmetricRationalMatrix M).map (Rat.castHom ℂ)) =
      (1/2 : ℂ) • (centralMatrixCLM (M.map (Rat.castHom ℂ))+
        (centralMatrixCLM (M.map (Rat.castHom ℂ))).adjoint) := by
  rw [symmetricRationalMatrix_cast, centralMatrixCLM_smul, centralMatrixCLM_add,
    centralMatrixCLM_conjTranspose]

theorem symmetric_operator_error
    (A B : EuclideanSpace ℂ (Fin 24) →L[ℂ] EuclideanSpace ℂ (Fin 24))
    (hA : A.adjoint = A) : ‖(1/2 : ℂ) • (B+B.adjoint)-A‖ ≤ ‖B-A‖ := by
  have hid : (1/2 : ℂ) • (B+B.adjoint)-A =
      (1/2 : ℂ) • ((B-A)+(B-A).adjoint) := by
    rw [map_sub, hA]
    module
  rw [hid, norm_smul]
  have hc : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  rw [hc]
  calc
    _ ≤ (1/2 : ℝ)*(‖B-A‖+‖(B-A).adjoint‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖B-A‖ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

end Maxwell.Continuum.Calibration
