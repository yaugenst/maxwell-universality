import Maxwell.Continuum.FiniteAuxiliaryMixed
import Maxwell.Composition.ComplexInverse

/-! Exact on-site bright compression and its dyadic diagonal-error bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass Maxwell.Composition

attribute [local irreducible] realMode Sh muH

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complexMatrixHom : Matrix ι ι ℝ →+* (BrightSpace ι →L[ℂ] BrightSpace ι) :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toRingEquiv.toRingHom.comp Complex.ofRealHom.mapMatrix

theorem complexOperator_add (A B : Matrix ι ι ℝ) :
    ComplexInverse.complexOperator (A+B) =
      ComplexInverse.complexOperator A+ComplexInverse.complexOperator B :=
  map_add (complexMatrixHom (ι := ι)) A B

theorem complexOperator_sub (A B : Matrix ι ι ℝ) :
    ComplexInverse.complexOperator (A-B) =
      ComplexInverse.complexOperator A-ComplexInverse.complexOperator B :=
  map_sub (complexMatrixHom (ι := ι)) A B

theorem complexOperator_neg (A : Matrix ι ι ℝ) :
    ComplexInverse.complexOperator (-A) = -ComplexInverse.complexOperator A :=
  map_neg (complexMatrixHom (ι := ι)) A

theorem complexDiagonal_apply (a : ι → ℝ) (f : BrightSpace ι) (i : ι) :
    ComplexInverse.complexOperator (Matrix.diagonal a) f i = (a i : ℂ)*f i := by
  change (∑ j, ((Matrix.diagonal a i j : ℝ) : ℂ)*f j) = _
  simp only [Matrix.diagonal_apply, apply_ite Complex.ofReal, Complex.ofReal_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem complexDiagonal_norm (a : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) (ha : ∀ i, |a i| ≤ c) :
    ‖ComplexInverse.complexOperator (Matrix.diagonal a)‖ ≤ c := by
  have he : ComplexInverse.complexOperator (Matrix.diagonal a) =
      diagonalBlocks (fun i => (a i : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
    apply ContinuousLinearMap.ext
    intro f
    apply PiLp.ext
    intro i
    rw [complexDiagonal_apply]
    rfl
  rw [he]
  apply diagonalBlocks_norm_le _ hc
  intro i
  simpa only [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs] using ha i

theorem onsite_bright {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (v : ι → ℝ) :
    (brightCoefficient (realMode D hh)).comp
      ((onsiteShift D hh v).comp (bright (realMode D hh))) =
      ComplexInverse.complexOperator (Matrix.diagonal fun i => (v i)⁻¹-muH D hh) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  rw [complexDiagonal_apply]
  change inner ℂ (realMode D hh) ((((v i)⁻¹-muH D hh : ℝ) : ℂ) • (f i • realMode D hh)) = _
  rw [inner_smul_right, inner_smul_right, inner_self_eq_norm_sq_to_K, realMode_norm]
  norm_num

theorem onsite_bright_error {h z R : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (v θ : ι → ℝ) (hR : 0 ≤ R)
    (hv : ∀ i, |(v i)⁻¹-(muH D hh+θ i)| ≤ R) :
    ‖(brightCoefficient (realMode D hh)).comp
      ((onsiteShift D hh v).comp (bright (realMode D hh)))-
      ComplexInverse.complexOperator (Matrix.diagonal θ)‖ ≤ R := by
  rw [onsite_bright]
  have he : ComplexInverse.complexOperator (Matrix.diagonal fun i => (v i)⁻¹-muH D hh)-
      ComplexInverse.complexOperator (Matrix.diagonal θ) =
      ComplexInverse.complexOperator (Matrix.diagonal fun i => (v i)⁻¹-(muH D hh+θ i)) := by
    apply ContinuousLinearMap.ext
    intro f
    apply PiLp.ext
    intro i
    simp only [sub_apply, PiLp.sub_apply, complexDiagonal_apply, Complex.ofReal_sub,
      Complex.ofReal_add]
    ring
  rw [he]
  exact complexDiagonal_norm _ hR hv

#print axioms onsite_bright_error

end Maxwell.Continuum.FiniteAuxiliary
