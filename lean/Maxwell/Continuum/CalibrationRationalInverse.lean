import Maxwell.Continuum.CalibrationRationalMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! A literal rational adjugate/determinant inverse for the fixed central
matrix. Its denominator is proved nonzero from the actual operator
invertibility established by the continuum approximation estimate. -/

namespace Maxwell.Continuum.Calibration

def rationalMatrixInverse (M : Matrix (Fin 24) (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℚ :=
  M.det⁻¹ • M.adjugate

theorem rationalMatrixInverse_cast (M : Matrix (Fin 24) (Fin 24) ℚ) :
    (rationalMatrixInverse M).map (Rat.castHom ℂ) = (M.map (Rat.castHom ℂ))⁻¹ := by
  have hd : (M.det : ℂ) = (M.map (Rat.castHom ℂ)).det := (Rat.castHom ℂ).map_det M
  have ha : M.adjugate.map (Rat.castHom ℂ) = (M.map (Rat.castHom ℂ)).adjugate :=
    (Rat.castHom ℂ).map_adjugate M
  rw [Matrix.inv_def, Ring.inverse_eq_inv, ← hd, ← ha]
  ext i j
  change (((M.det⁻¹ : ℚ)*M.adjugate i j : ℚ) : ℂ) =
    (M.det : ℂ)⁻¹*(M.adjugate i j : ℂ)
  simp only [Rat.cast_mul, Rat.cast_inv]

theorem centralMatrixCLM_eq (M : Matrix (Fin 24) (Fin 24) ℂ) :
    centralMatrixCLM M = Matrix.toEuclideanCLM (n := Fin 24) (𝕜 := ℂ) M := rfl

theorem rationalMatrix_det_ne_zero (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hM : IsUnit (centralMatrixCLM (M.map (Rat.castHom ℂ)))) : M.det ≠ 0 := by
  rw [centralMatrixCLM_eq] at hM
  have hm := hM.map (Matrix.toEuclideanCLM (n := Fin 24) (𝕜 := ℂ)).symm.toMonoidHom
  change IsUnit ((Matrix.toEuclideanCLM (n := Fin 24) (𝕜 := ℂ)).symm
    (Matrix.toEuclideanCLM (n := Fin 24) (𝕜 := ℂ) (M.map (Rat.castHom ℂ)))) at hm
  rw [StarAlgEquiv.symm_apply_apply] at hm
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hm
  have hdcast : (M.det : ℂ) = (M.map (Rat.castHom ℂ)).det := (Rat.castHom ℂ).map_det M
  rw [← hdcast] at hd
  intro h
  rw [h, Rat.cast_zero] at hd
  exact not_isUnit_zero hd

theorem rationalMatrixInverse_sound (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hM : IsUnit (centralMatrixCLM (M.map (Rat.castHom ℂ)))) :
    centralMatrixCLM ((rationalMatrixInverse M).map (Rat.castHom ℂ)) =
      Ring.inverse (centralMatrixCLM (M.map (Rat.castHom ℂ))) := by
  have hd : IsUnit (M.map (Rat.castHom ℂ)).det := by
    have hdcast : (M.det : ℂ) = (M.map (Rat.castHom ℂ)).det := (Rat.castHom ℂ).map_det M
    rw [← hdcast]
    apply isUnit_iff_ne_zero.mpr
    exact_mod_cast rationalMatrix_det_ne_zero M hM
  have hprod : centralMatrixCLM (M.map (Rat.castHom ℂ))*
      centralMatrixCLM ((rationalMatrixInverse M).map (Rat.castHom ℂ)) = 1 := by
    rw [rationalMatrixInverse_cast, centralMatrixCLM_eq, centralMatrixCLM_eq,
      ← map_mul, Matrix.mul_nonsing_inv _ hd, map_one]
  calc
    _ = 1*centralMatrixCLM ((rationalMatrixInverse M).map (Rat.castHom ℂ)) := (one_mul _).symm
    _ = (Ring.inverse (centralMatrixCLM (M.map (Rat.castHom ℂ)))*
      centralMatrixCLM (M.map (Rat.castHom ℂ)))*
        centralMatrixCLM ((rationalMatrixInverse M).map (Rat.castHom ℂ)) := by
      rw [Ring.inverse_mul_cancel _ hM]
    _ = _ := by rw [mul_assoc,hprod,mul_one]

#print axioms rationalMatrixInverse_sound

end Maxwell.Continuum.Calibration
