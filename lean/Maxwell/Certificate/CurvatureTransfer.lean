import Maxwell.Certificate.CorrectorWitness.Saved
import Maxwell.Certificate.FrozenHessian.LppmLower
import Maxwell.Certificate.FrozenHessian.LppmUpper
import Maxwell.Spectral.JetTransfer
import Maxwell.Spectral.Trial

namespace Maxwell.Certificate.CurvatureTransfer

open Matrix Maxwell.Spectral Maxwell.Spectral.YeeTaylor
open Maxwell.Spectral.PeriodicYee (Momentum)
noncomputable section

section MatrixEstimates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realMatrixOperator (A : Matrix ι ι ℝ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (A.map Complex.ofReal)

theorem realMatrixOperator_quadratic (A : Matrix ι ι ℝ) (x : EuclideanSpace ℂ ι) :
    Complex.re (inner ℂ x (realMatrixOperator A x)) =
      (fun i => (x i).re) ⬝ᵥ (A *ᵥ fun i => (x i).re) +
      (fun i => (x i).im) ⬝ᵥ (A *ᵥ fun i => (x i).im) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm]
  change Complex.re (star (fun i => x i) ⬝ᵥ ((A.map Complex.ofReal) *ᵥ fun i => x i)) = _
  simp only [dotProduct, mulVec, Finset.mul_sum, Complex.re_sum, Matrix.map_apply,
    Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq ι] in
theorem complex_norm_sq_real_imag (x : EuclideanSpace ℂ ι) :
    ‖x‖^2 = (fun i => (x i).re) ⬝ᵥ (fun i => (x i).re) +
      (fun i => (x i).im) ⬝ᵥ (fun i => (x i).im) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, Complex.sq_norm, Complex.normSq_apply, ← Finset.sum_add_distrib]

theorem realMatrixOperator_lower (A : Matrix ι ι ℝ) (a : ℝ)
    (hA : (A - a • (1 : Matrix ι ι ℝ)).PosSemidef) (x : EuclideanSpace ℂ ι) :
    a * ‖x‖^2 ≤ Complex.re (inner ℂ x (realMatrixOperator A x)) := by
  have hr := hA.dotProduct_mulVec_nonneg (fun i => (x i).re)
  have hi := hA.dotProduct_mulVec_nonneg (fun i => (x i).im)
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    star_trivial, smul_eq_mul] at hr hi
  rw [realMatrixOperator_quadratic, complex_norm_sq_real_imag]
  nlinarith only [hr, hi]

theorem realMatrixOperator_upper (A : Matrix ι ι ℝ) (a : ℝ)
    (hA : (a • (1 : Matrix ι ι ℝ) - A).PosSemidef) (x : EuclideanSpace ℂ ι) :
    Complex.re (inner ℂ x (realMatrixOperator A x)) ≤ a * ‖x‖^2 := by
  have hr := hA.dotProduct_mulVec_nonneg (fun i => (x i).re)
  have hi := hA.dotProduct_mulVec_nonneg (fun i => (x i).im)
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    star_trivial, smul_eq_mul] at hr hi
  rw [realMatrixOperator_quadratic, complex_norm_sq_real_imag]
  nlinarith only [hr, hi]

theorem complexMatrixOperator_norm_le (A : Matrix ι ι ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : ∀ i j, ‖A i j‖ ≤ ε) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A‖ ≤ Fintype.card ι * ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hrow (i : ι) : ∑ j, ‖A i j‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ε^2 := by
    calc
      _ ≤ ∑ _j : ι, ε^2 := Finset.sum_le_sum (fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hA i j) 2)
      _ = _ := by simp
  have hrowx (i : ι) : ‖∑ j, A i j * x j‖^2 ≤
      ((Fintype.card ι : ℝ) * ε^2) * ∑ j, ‖x j‖^2 := by
    have ht : ‖∑ j, A i j * x j‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ :=
      (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
    calc
      _ ≤ (∑ j, ‖A i j‖ * ‖x j‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) ht 2
      _ ≤ (∑ j, ‖A i j‖^2) * ∑ j, ‖x j‖^2 :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖) (fun j => ‖x j‖)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hsq : ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A x‖^2 ≤
      ((Fintype.card ι : ℝ) * ε * ‖x‖)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : ι, ((Fintype.card ι : ℝ) * ε^2) * ∑ j, ‖x j‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact hrowx i
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← EuclideanSpace.norm_sq_eq]
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

theorem realMatrixOperator_entry_error (A B : Matrix ι ι ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hentry : ∀ i j, |A i j - B i j| ≤ ε) :
    ‖realMatrixOperator A - realMatrixOperator B‖ ≤ Fintype.card ι * ε := by
  have heq : realMatrixOperator A - realMatrixOperator B =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) ((A - B).map Complex.ofReal) := by
    unfold realMatrixOperator
    rw [← map_sub]
    congr 1
    ext i j
    simp
  rw [heq]
  apply complexMatrixOperator_norm_le _ ε hε
  intro i j
  simpa only [Matrix.map_apply, Matrix.sub_apply, Complex.norm_real, Real.norm_eq_abs] using hentry i j

end MatrixEstimates

def directionalHalf (H : Matrix (Fin 6) (Fin 6) ℝ) (q : Momentum) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (1/2 : ℂ) • (CorrectorWitness.directionCoefficients q).adjoint.comp
    ((realMatrixOperator H).comp (CorrectorWitness.directionCoefficients q))

theorem directionalHalf_quadratic (H : Matrix (Fin 6) (Fin 6) ℝ)
    (q : Momentum) (x : EuclideanSpace ℂ (Fin 2)) :
    Complex.re (inner ℂ x (directionalHalf H q x)) =
      (1/2 : ℝ) * Complex.re (inner ℂ (CorrectorWitness.directionCoefficients q x)
        (realMatrixOperator H (CorrectorWitness.directionCoefficients q x))) := by
  simp only [directionalHalf, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
  simp

theorem directionalHalf_rounded_bounds (q : Momentum) (x : EuclideanSpace ℂ (Fin 2)) :
    (2003/100000 : ℝ) * radius q^2 * ‖x‖^2 ≤
        Complex.re (inner ℂ x (directionalHalf FrozenHessian.lppm q x)) ∧
      Complex.re (inner ℂ x (directionalHalf FrozenHessian.lppm q x)) ≤
        (49997/100000 : ℝ) * radius q^2 * ‖x‖^2 := by
  have hl := realMatrixOperator_lower FrozenHessian.lppm (2003/50000)
    FrozenHessian.lppm_lower_psd (CorrectorWitness.directionCoefficients q x)
  have hu := realMatrixOperator_upper FrozenHessian.lppm (49997/50000)
    FrozenHessian.lppm_upper_psd (CorrectorWitness.directionCoefficients q x)
  rw [CorrectorWitness.directionCoefficients_norm_sq] at hl hu
  rw [directionalHalf_quadratic]
  constructor <;> linarith

theorem directionalHalf_error (H G : Matrix (Fin 6) (Fin 6) ℝ)
    (q : Momentum) (ε : ℝ) (hε : 0 ≤ ε)
    (hentry : ∀ i j, |H i j - G i j| ≤ ε) :
    ‖directionalHalf H q - directionalHalf G q‖ ≤ 3 * ε * radius q^2 := by
  have he : directionalHalf H q - directionalHalf G q =
      (1/2 : ℂ) • (CorrectorWitness.directionCoefficients q).adjoint.comp
        ((realMatrixOperator H - realMatrixOperator G).comp
          (CorrectorWitness.directionCoefficients q)) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, smul_sub]
    rfl
  rw [he, norm_smul]
  have hc : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  rw [hc]
  have hentry' : ‖realMatrixOperator H - realMatrixOperator G‖ ≤ 6 * ε := by
    simpa using realMatrixOperator_entry_error H G ε hε hentry
  have hd := CorrectorWitness.directionCoefficients_norm_le q
  have ha : ‖(CorrectorWitness.directionCoefficients q).adjoint‖ ≤ radius q := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hd
  have hb : ‖(realMatrixOperator H - realMatrixOperator G).comp
      (CorrectorWitness.directionCoefficients q)‖ ≤ (6*ε) * radius q :=
    norm_comp_of_bounds _ _ _ _ hentry' hd (by positivity)
  calc
    _ ≤ (1/2 : ℝ) * (radius q * ((6*ε) * radius q)) :=
      mul_le_mul_of_nonneg_left
        (((CorrectorWitness.directionCoefficients q).adjoint.opNorm_comp_le _).trans
          (mul_le_mul ha hb (norm_nonneg _) (radius_nonneg q))) (by norm_num)
    _ = _ := by ring

/-- The finite Hessian entry certificate and an independently proved
operator replacement error imply the advertised directional forms. -/
theorem directional_bounds_of_approximation
    (H : Matrix (Fin 6) (Fin 6) ℝ) (q : Momentum)
    (K : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
    (hentry : ∀ i j, |H i j - FrozenHessian.lppm i j| ≤ 1 / 10^11)
    (hreplace : ‖K - directionalHalf H q‖ ≤ (1/1000000 : ℝ) * radius q^2)
    (x : EuclideanSpace ℂ (Fin 2)) :
    radius q^2 * ‖x‖^2 / 50 ≤ Complex.re (inner ℂ x (K x)) ∧
      Complex.re (inner ℂ x (K x)) ≤ radius q^2 * ‖x‖^2 := by
  have hr := directionalHalf_error H FrozenHessian.lppm q (1/10^11) (by positivity) hentry
  have he : ‖K - directionalHalf FrozenHessian.lppm q‖ ≤
      (1/1000000 + 3/10^11 : ℝ) * radius q^2 := by
    calc
      _ ≤ ‖K - directionalHalf H q‖ + ‖directionalHalf H q -
          directionalHalf FrozenHessian.lppm q‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by nlinarith only [hreplace, hr]
  have hb := directionalHalf_rounded_bounds q x
  have hl := JetTransfer.quadratic_lower_transfer K (directionalHalf FrozenHessian.lppm q)
    ((2003/100000 : ℝ) * radius q^2)
    ((1/1000000 + 3/10^11 : ℝ) * radius q^2) he
    (fun y => (directionalHalf_rounded_bounds q y).1) x
  have hu := JetTransfer.quadratic_upper_transfer K (directionalHalf FrozenHessian.lppm q)
    ((49997/100000 : ℝ) * radius q^2)
    ((1/1000000 + 3/10^11 : ℝ) * radius q^2) he
    (fun y => (directionalHalf_rounded_bounds q y).2) x
  have hp : 0 ≤ radius q^2 * ‖x‖^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  constructor <;> nlinarith only [hl, hu, hp]

end
end Maxwell.Certificate.CurvatureTransfer
