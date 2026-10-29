import Maxwell.Spectral.BoxSymbols
import Maxwell.Certificate.FourierCoercivity
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Dimension-independent operator bounds for the actual Fourier curl.
The complex Lagrange identity controls each three-component block; summing
squared block norms introduces no factor depending on the frequency count. -/

noncomputable section

namespace Maxwell.Spectral.BoxCrossNorm

open Matrix Maxwell.Certificate.FourierBinding
open Maxwell.Spectral.PeriodicYee (Direction Momentum)
open scoped ComplexConjugate

def crossMatrix (d : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, -d 2, d 1; d 2, 0, -d 0; -d 1, d 0, 0]

/-- The complex cross product has the same Gram determinant identity as
its real counterpart, with the Hermitian inner product in the last term. -/
theorem complex_lagrange (d x : Fin 3 → ℂ) :
    (∑ i, Complex.normSq ((crossMatrix d *ᵥ x) i)) +
        Complex.normSq (∑ i, conj (d i) * x i) =
      (∑ i, Complex.normSq (d i)) * (∑ i, Complex.normSq (x i)) := by
  simp [crossMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem crossMatrix_apply_norm (d : Fin 3 → ℂ) (x : EuclideanSpace ℂ (Fin 3)) :
    ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) (crossMatrix d) x‖ ≤
      ‖(WithLp.toLp 2 d : EuclideanSpace ℂ (Fin 3))‖ * ‖x‖ := by
  have h := complex_lagrange d x.ofLp
  have hp := Complex.normSq_nonneg (∑ i, conj (d i) * x i)
  have hsq : ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) (crossMatrix d) x‖^2 ≤
      (‖(WithLp.toLp 2 d : EuclideanSpace ℂ (Fin 3))‖ * ‖x‖)^2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖(crossMatrix d *ᵥ x.ofLp) i‖^2) ≤ (∑ i, ‖d i‖^2) * (∑ i, ‖x i‖^2)
    have hle : (∑ i, Complex.normSq ((crossMatrix d *ᵥ x.ofLp) i)) ≤
        (∑ i, Complex.normSq (d i)) * (∑ i, Complex.normSq (x i)) := by linarith
    simpa only [Complex.normSq_eq_norm_sq] using hle
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsq

theorem crossMatrix_norm (d : Fin 3 → ℂ) :
    ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) (crossMatrix d)‖ ≤
      ‖(WithLp.toLp 2 d : EuclideanSpace ℂ (Fin 3))‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (crossMatrix_apply_norm d)

theorem crossMatrix_sub (d e : Fin 3 → ℂ) : crossMatrix (d - e) = crossMatrix d - crossMatrix e := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossMatrix] <;> ring

def directSumMatrix {F : Type*} [DecidableEq F] (K : F → Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3 × F) (Fin 3 × F) ℂ := fun i j =>
  if i.2 = j.2 then K i.2 i.1 j.1 else 0

def blockMatrix {F : Type*} [DecidableEq F] (d : F → Fin 3 → ℂ) :
    Matrix (Fin 3 × F) (Fin 3 × F) ℂ := directSumMatrix (fun f => crossMatrix (d f))

def blockComponent {F : Type*} (x : EuclideanSpace ℂ (Fin 3 × F)) (f : F) :
    EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 fun j => x (j, f)

theorem directSumMatrix_component {F : Type*} [Fintype F] [DecidableEq F]
    (K : F → Matrix (Fin 3) (Fin 3) ℂ) (x : EuclideanSpace ℂ (Fin 3 × F)) (f : F) :
    blockComponent (Matrix.toEuclideanCLM (n := Fin 3 × F) (𝕜 := ℂ) (directSumMatrix K) x) f =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) (K f) (blockComponent x f) := by
  apply WithLp.ofLp_injective 2
  funext i
  change (directSumMatrix K *ᵥ x.ofLp) (i, f) = (K f *ᵥ (fun j => x (j, f))) i
  simp [directSumMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

theorem blockMatrix_component {F : Type*} [Fintype F] [DecidableEq F]
    (d : F → Fin 3 → ℂ) (x : EuclideanSpace ℂ (Fin 3 × F)) (f : F) :
    blockComponent (Matrix.toEuclideanCLM (n := Fin 3 × F) (𝕜 := ℂ) (blockMatrix d) x) f =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) (crossMatrix (d f)) (blockComponent x f) :=
  directSumMatrix_component _ x f

theorem norm_sq_eq_sum_blocks {F : Type*} [Fintype F]
    (x : EuclideanSpace ℂ (Fin 3 × F)) : ‖x‖^2 = ∑ f, ‖blockComponent x f‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rfl

theorem directSumMatrix_apply_norm {F : Type*} [Fintype F] [DecidableEq F]
    (K : F → Matrix (Fin 3) (Fin 3) ℂ) (s : ℝ) (hs : 0 ≤ s)
    (hK : ∀ f, ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) (K f)‖ ≤ s)
    (x : EuclideanSpace ℂ (Fin 3 × F)) :
    ‖Matrix.toEuclideanCLM (n := Fin 3 × F) (𝕜 := ℂ) (directSumMatrix K) x‖ ≤ s * ‖x‖ := by
  have hsq : ‖Matrix.toEuclideanCLM (n := Fin 3 × F) (𝕜 := ℂ) (directSumMatrix K) x‖^2 ≤
      (s * ‖x‖)^2 := by
    rw [mul_pow, norm_sq_eq_sum_blocks, norm_sq_eq_sum_blocks, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro f _
    rw [directSumMatrix_component]
    have hf := ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) (K f)).le_opNorm (blockComponent x f)).trans
      (mul_le_mul_of_nonneg_right (hK f) (norm_nonneg _))
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hf 2
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hs (norm_nonneg _))).mp hsq

theorem directSumMatrix_norm {F : Type*} [Fintype F] [DecidableEq F]
    (K : F → Matrix (Fin 3) (Fin 3) ℂ) (s : ℝ) (hs : 0 ≤ s)
    (hK : ∀ f, ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) (K f)‖ ≤ s) :
    ‖Matrix.toEuclideanCLM (n := Fin 3 × F) (𝕜 := ℂ) (directSumMatrix K)‖ ≤ s :=
  ContinuousLinearMap.opNorm_le_bound _ hs (directSumMatrix_apply_norm K s hs hK)

theorem blockMatrix_apply_norm {F : Type*} [Fintype F] [DecidableEq F]
    (d : F → Fin 3 → ℂ) (s : ℝ) (hs : 0 ≤ s)
    (hd : ∀ f, ‖(WithLp.toLp 2 (d f) : EuclideanSpace ℂ (Fin 3))‖ ≤ s)
    (x : EuclideanSpace ℂ (Fin 3 × F)) :
    ‖Matrix.toEuclideanCLM (n := Fin 3 × F) (𝕜 := ℂ) (blockMatrix d) x‖ ≤ s * ‖x‖ :=
  directSumMatrix_apply_norm _ s hs (fun f => (crossMatrix_norm (d f)).trans (hd f)) x

theorem blockMatrix_norm {F : Type*} [Fintype F] [DecidableEq F]
    (d : F → Fin 3 → ℂ) (s : ℝ) (hs : 0 ≤ s)
    (hd : ∀ f, ‖(WithLp.toLp 2 (d f) : EuclideanSpace ℂ (Fin 3))‖ ≤ s) :
    ‖Matrix.toEuclideanCLM (n := Fin 3 × F) (𝕜 := ℂ) (blockMatrix d)‖ ≤ s :=
  ContinuousLinearMap.opNorm_le_bound _ hs (blockMatrix_apply_norm d s hs hd)

theorem blockMatrix_sub {F : Type*} [DecidableEq F] (d e : F → Fin 3 → ℂ) :
    blockMatrix (d - e) = blockMatrix d - blockMatrix e := by
  ext i j
  by_cases h : i.2 = j.2
  · simp [blockMatrix, directSumMatrix, h, crossMatrix_sub]
  · simp [blockMatrix, directSumMatrix, h]

theorem frequency_norm_sq_eq_sum (x : FourierSpace) :
    ‖x‖^2 = ∑ f, ‖frequencyComponent f x‖^2 := norm_sq_eq_sum_blocks x

/-- The abstract blocks are exactly the genuine primitive Fourier curl. -/
theorem frequencyCurl_eq_blocks (c : Momentum) : frequencyCurl c = blockMatrix (symbol c) := rfl

/-- The exact linear Taylor term of the genuine frequency curl. -/
def linearFrequencyCurl (c q : Momentum) :
    Matrix Maxwell.Spectral.PrimitiveYee.Electric Maxwell.Spectral.PrimitiveYee.Electric ℂ :=
  blockMatrix (BoxSymbols.linearSymbol c q)

theorem linearVector_norm (c q : Momentum) (f : Frequency) :
    ‖BoxSymbols.linearVector c q f‖ = BoxSymbols.phaseScale * BoxSymbols.momentumNorm q := by
  have hj (j : Direction) : ‖BoxSymbols.linearSymbol c q f j‖ =
      BoxSymbols.phaseScale * |q j| := by
    simp [BoxSymbols.linearSymbol, BoxSymbols.shiftSymbol_norm,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos BoxSymbols.phaseScale_pos]
  have hsq : ‖BoxSymbols.linearVector c q f‖^2 =
      (BoxSymbols.phaseScale * BoxSymbols.momentumNorm q)^2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, BoxSymbols.momentumNorm_sq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change ‖BoxSymbols.linearSymbol c q f j‖^2 = _
    rw [hj, mul_pow, sq_abs]
  exact (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg BoxSymbols.phaseScale_pos.le (norm_nonneg _))).mp hsq

theorem linearFrequencyCurl_norm (c q : Momentum) :
    ‖Matrix.toEuclideanCLM (n := Maxwell.Spectral.PrimitiveYee.Electric) (𝕜 := ℂ)
      (linearFrequencyCurl c q)‖ ≤ BoxSymbols.phaseScale * BoxSymbols.momentumNorm q :=
  blockMatrix_norm _ _ (mul_nonneg BoxSymbols.phaseScale_pos.le (norm_nonneg _))
    (fun f => (linearVector_norm c q f).le)

theorem frequencyCurl_increment_eq (c q : Momentum) :
    frequencyCurl (c + q) - frequencyCurl c = blockMatrix (symbol (c + q) - symbol c) := by
  rw [blockMatrix_sub]
  rfl

theorem frequencyCurl_increment_norm (c q : Momentum) :
    ‖Matrix.toEuclideanCLM (n := Maxwell.Spectral.PrimitiveYee.Electric) (𝕜 := ℂ)
      (frequencyCurl (c + q) - frequencyCurl c)‖ ≤
        BoxSymbols.phaseScale * BoxSymbols.momentumNorm q := by
  rw [frequencyCurl_increment_eq]
  exact blockMatrix_norm _ _ (mul_nonneg BoxSymbols.phaseScale_pos.le (norm_nonneg _))
    (BoxSymbols.incrementVector_norm c q)

theorem frequencyCurl_linear_remainder_norm (c q : Momentum) :
    ‖Matrix.toEuclideanCLM (n := Maxwell.Spectral.PrimitiveYee.Electric) (𝕜 := ℂ)
      (frequencyCurl (c + q) - frequencyCurl c - linearFrequencyCurl c q)‖ ≤
        BoxSymbols.phaseScale^2 * BoxSymbols.momentumNorm q^2 / 2 := by
  rw [frequencyCurl_increment_eq]
  change ‖Matrix.toEuclideanCLM (n := Maxwell.Spectral.PrimitiveYee.Electric) (𝕜 := ℂ)
    (blockMatrix (symbol (c + q) - symbol c) - blockMatrix (BoxSymbols.linearSymbol c q))‖ ≤ _
  rw [← blockMatrix_sub]
  exact blockMatrix_norm _ _ (by positivity) (BoxSymbols.incrementVector_linear_remainder c q)

end Maxwell.Spectral.BoxCrossNorm
