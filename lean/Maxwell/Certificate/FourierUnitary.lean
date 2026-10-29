import Maxwell.Certificate.FourierBinding
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Unitarity of the concrete FCC Fourier basis, from the unitary primitive
shifts and their distinct joint Fourier eigenvalues. -/

noncomputable section

namespace Maxwell.Certificate.FourierBinding

open Matrix Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction Momentum)

theorem planeWave_unit (c : Momentum) (f : Frequency) (r : RawCell) :
    star (planeWave c f r) * planeWave c f r = 1 := by
  change starRingEnd ℂ (Complex.exp _) * Complex.exp _ = 1
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem normalization_square : star normalization * normalization = (2000 : ℂ)⁻¹ := by
  have hs : (((Real.sqrt 2000 : ℝ) : ℂ)) ^ 2 = (2000 : ℂ) := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2000))
  calc
    _ = ((((Real.sqrt 2000 : ℝ) : ℂ)) ^ 2)⁻¹ := by
      simp [normalization, pow_two]
    _ = _ := by rw [hs]

theorem basis_square (c : Momentum) (f : Frequency) (p : Cell) :
    star (basis c f p) * basis c f p = (2000 : ℂ)⁻¹ := by
  calc
    _ = (star normalization * normalization) *
        (star (planeWave c f (representative p)) * planeWave c f (representative p)) := by
      simp only [basis, star_mul]
      ring
    _ = _ := by rw [planeWave_unit, mul_one, normalization_square]

theorem transform_gram_diagonal (c : Momentum) (f : Frequency) :
    ((transform c).conjTranspose * transform c) f f = 1 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, transform, basis_square]
  norm_num [Cell, Frequency]

theorem shift_transform (c : Momentum) (j : Direction) :
    shift (boundaryMomentum c) j * transform c =
      transform c * Matrix.diagonal (fun f => shiftSymbol c f j) := by
  ext p f
  rw [Matrix.mul_diagonal]
  simpa only [Matrix.mul_apply, transform, Matrix.mulVec, dotProduct, mul_comm] using
    shift_basis c f j p

theorem integer_phase_injective (a b : ℤ) (c : ℝ)
    (hlo : -20 < a - b) (hhi : a - b < 20)
    (he : Complex.exp (Complex.I * ((2 * Real.pi / 20 * ((a : ℝ) + c)) : ℂ)) =
      Complex.exp (Complex.I * ((2 * Real.pi / 20 * ((b : ℝ) + c)) : ℂ))) : a = b := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have him := congrArg Complex.im hn
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, zero_add, Complex.add_im, Complex.intCast_re,
    Complex.intCast_im, mul_zero, add_zero] at him
  norm_num at him
  have hzero : (2 * Real.pi / 20) * ((a : ℝ) - b - 20 * n) = 0 := by
    linear_combination him
  have hcoef : 2 * Real.pi / 20 ≠ 0 := by positivity
  have hrel : (a : ℝ) - b - 20 * n = 0 := (mul_eq_zero.mp hzero).resolve_left hcoef
  have hZ : a - b = 20 * n := by exact_mod_cast (show (a : ℝ) - b = 20 * n by linarith)
  omega

theorem joint_shiftSymbol_injective (c : Momentum) :
    Function.Injective (fun f : Frequency => shiftSymbol c f) := by
  intro f g he
  have hx := integer_phase_injective (reciprocalIndex f 0) (reciprocalIndex g 0) (c 0)
    (by simp only [reciprocalIndex, Matrix.cons_val_zero]; have := f.1.isLt; have := g.1.isLt; omega)
    (by simp only [reciprocalIndex, Matrix.cons_val_zero]; have := f.1.isLt; have := g.1.isLt; omega)
    (congrFun he 0)
  have hfx : (f.1.val : ℤ) = g.1.val := by simpa [reciprocalIndex] using hx
  have hy := integer_phase_injective (reciprocalIndex f 1) (reciprocalIndex g 1) (c 1)
    (by simp [reciprocalIndex]; have := f.2.1.isLt; have := g.2.1.isLt; omega)
    (by simp [reciprocalIndex]; have := f.2.1.isLt; have := g.2.1.isLt; omega)
    (congrFun he 1)
  have hz := integer_phase_injective (reciprocalIndex f 2) (reciprocalIndex g 2) (c 2)
    (by simp [reciprocalIndex]; have := f.2.2.isLt; have := g.2.2.isLt; omega)
    (by simp [reciprocalIndex]; have := f.2.2.isLt; have := g.2.2.isLt; omega)
    (congrFun he 2)
  apply Prod.ext
  · apply Fin.ext
    omega
  · apply Prod.ext <;> apply Fin.ext
    · simp [reciprocalIndex] at hy
      omega
    · simp [reciprocalIndex] at hz
      omega

theorem unitary_eigenvectors_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U F : Matrix ι ι ℂ) (eig : ι → ℂ) (hU : U.conjTranspose * U = 1)
    (hF : U * F = F * Matrix.diagonal eig) (i j : ι)
    (hi : star (eig i) * eig i = 1) (hne : eig i ≠ eig j) :
    (F.conjTranspose * F) i j = 0 := by
  have he : (F * Matrix.diagonal eig).conjTranspose * (F * Matrix.diagonal eig) =
      F.conjTranspose * F := by
    rw [← hF, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc U.conjTranspose U F, hU,
      Matrix.one_mul]
  have he' : Matrix.diagonal (star eig) * (F.conjTranspose * F) *
      Matrix.diagonal eig = F.conjTranspose * F := by
    simpa only [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose,
      Matrix.mul_assoc] using he
  have heij := congrFun (congrFun he' i) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply] at heij
  have hi' : eig i * star (eig i) = 1 := by simpa only [mul_comm] using hi
  have hm := congrArg (fun z => eig i * z) heij
  have hr : eig i * ((star (eig i) * (F.conjTranspose * F) i j) * eig j) =
      (eig i * star (eig i)) * (eig j * (F.conjTranspose * F) i j) := by ring
  rw [hr, hi', one_mul] at hm
  by_contra hzero
  exact hne (mul_right_cancel₀ hzero hm).symm

theorem shiftSymbol_unit (c : Momentum) (f : Frequency) (j : Direction) :
    star (shiftSymbol c f j) * shiftSymbol c f j = 1 := by
  rw [← planeWave_rawUnit]
  exact planeWave_unit _ _ _

theorem transform_conjTranspose_mul (c : Momentum) :
    (transform c).conjTranspose * transform c = 1 := by
  ext f g
  by_cases hfg : f = g
  · subst g
    simp only [transform_gram_diagonal, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hfg]
    have hne : ∃ j, shiftSymbol c f j ≠ shiftSymbol c g j := by
      by_contra hh
      push Not at hh
      exact hfg (joint_shiftSymbol_injective c (funext hh))
    obtain ⟨j, hj⟩ := hne
    exact unitary_eigenvectors_orthogonal (shift (boundaryMomentum c) j) (transform c)
      (fun f => shiftSymbol c f j) (shift_conjTranspose_mul _ _) (shift_transform c j)
      f g (shiftSymbol_unit c f j) hj

theorem transform_mul_conjTranspose (c : Momentum) :
    transform c * (transform c).conjTranspose = 1 :=
  mul_eq_one_comm.mp (transform_conjTranspose_mul c)

theorem electricTransform_conjTranspose_mul (c : Momentum) :
    (electricTransform c).conjTranspose * electricTransform c = 1 := by
  ext ⟨i, p⟩ ⟨j, q⟩
  have h := congrFun (congrFun (transform_conjTranspose_mul c) p) q
  by_cases hij : i = j
  · subst j
    simpa [electricTransform, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, ite_mul, mul_ite, transform, Matrix.one_apply] using h
  · simp [electricTransform, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, mul_ite, hij, Ne.symm hij]

theorem electricTransform_mul_conjTranspose (c : Momentum) :
    electricTransform c * (electricTransform c).conjTranspose = 1 :=
  mul_eq_one_comm.mp (electricTransform_conjTranspose_mul c)

theorem difference_diagonalized (c : Momentum) (j : Direction) :
    (transform c).conjTranspose * difference (boundaryMomentum c) j * transform c =
      Matrix.diagonal (fun f => symbol c f j) := by
  rw [Matrix.mul_assoc, difference_transform, ← Matrix.mul_assoc,
    transform_conjTranspose_mul, Matrix.one_mul]

theorem curl_diagonalized (c : Momentum) :
    (electricTransform c).conjTranspose * curl (boundaryMomentum c) * electricTransform c =
      frequencyCurl c := by
  rw [Matrix.mul_assoc, curl_transform, ← Matrix.mul_assoc,
    electricTransform_conjTranspose_mul, Matrix.one_mul]

theorem curl_adjoint_diagonalized (c : Momentum) :
    (electricTransform c).conjTranspose * (curl (boundaryMomentum c)).conjTranspose *
        electricTransform c = (frequencyCurl c).conjTranspose := by
  have h := congrArg Matrix.conjTranspose (curl_diagonalized c)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc] using h

theorem unitary_compression_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U A B : Matrix ι ι ℂ) (hU : U * U.conjTranspose = 1) :
    U.conjTranspose * (A * B) * U =
      (U.conjTranspose * A * U) * (U.conjTranspose * B * U) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U U.conjTranspose, hU, Matrix.one_mul]

def fourierMass (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) :
    Matrix Electric Electric ℂ :=
  (electricTransform c).conjTranspose * mass material * electricTransform c

def fourierFiber (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) :
    Matrix Electric Electric ℂ :=
  (frequencyCurl c).conjTranspose * frequencyCurl c - (1 / 64 : ℂ) • fourierMass material c

theorem fiber_diagonalized (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) :
    (electricTransform c).conjTranspose * fiber material (boundaryMomentum c) *
        electricTransform c = fourierFiber material c := by
  unfold fiber fourierFiber fourierMass
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [unitary_compression_mul _ _ _ (electricTransform_mul_conjTranspose c),
    curl_adjoint_diagonalized, curl_diagonalized]

end Maxwell.Certificate.FourierBinding
