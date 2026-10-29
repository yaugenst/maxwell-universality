import Maxwell.Spectral.ConventionalReality

namespace Maxwell.Spectral.ConventionalAnalytic

open Maxwell.Spectral.PeriodicYee
noncomputable section
set_option maxRecDepth 4000

def reflectMomentum (z : ComplexMomentum) : ComplexMomentum := fun j => -star (z j)

theorem reflectMomentum_continuous : Continuous reflectMomentum := by
  unfold reflectMomentum
  fun_prop

@[simp] theorem reflectMomentum_zero : reflectMomentum 0 = 0 := by
  ext j
  simp [reflectMomentum]

@[simp] theorem reflectMomentum_neg (z : ComplexMomentum) :
    reflectMomentum (-z) = -reflectMomentum z := by
  ext j
  simp [reflectMomentum]

theorem realMomentum_trim_neg (k : Direction → ℤ) :
    realMomentum (trim (-k)) = -realMomentum (trim k) := by
  ext j
  simp [realMomentum, trim]

theorem boundaryPhase_trim_reflection (k : Direction → ℤ) (z : ComplexMomentum)
    (j : Direction) (r : Cell20) :
    boundaryPhase (realMomentum (trim k) + reflectMomentum z) j r =
      star (boundaryPhase (realMomentum (trim k) + z) j r) := by
  unfold boundaryPhase
  split_ifs
  · have ht : star (Complex.exp (Complex.I * realMomentum (trim k) j)) =
        Complex.exp (Complex.I * realMomentum (trim k) j) := by
      change star (Complex.exp (Complex.I * ((trim k j : ℝ) : ℂ))) =
        Complex.exp (Complex.I * ((trim k j : ℝ) : ℂ))
      rw [trim_exp]
      simp
    simp only [Pi.add_apply, reflectMomentum, mul_add, Complex.exp_add,
      star_mul, ht]
    rw [mul_comm]
    congr 1
    rw [show star (Complex.exp (Complex.I * z j)) =
      Complex.exp (star (Complex.I * z j)) from (Complex.exp_conj _).symm]
    simp
  · simp

theorem difference_trim_reflection (k : Direction → ℤ) (z : ComplexMomentum)
    (j : Direction) (r s : Cell20) :
    difference (realMomentum (trim k) + reflectMomentum z) j r s =
      star (difference (realMomentum (trim k) + z) j r s) := by
  unfold difference
  split_ifs <;> simp [boundaryPhase_trim_reflection]

theorem curl_trim_reflection (k : Direction → ℤ) (z : ComplexMomentum)
    (i : Face20) (j : Electric20) :
    curl (realMomentum (trim k) + reflectMomentum z) i j =
      star (curl (realMomentum (trim k) + z) i j) := by
  unfold curl
  split_ifs <;> simp [difference_trim_reflection]

theorem formalAdjointCurl_trim_reflection (k : Direction → ℤ) (z : ComplexMomentum)
    (i : Electric20) (j : Face20) :
    formalAdjointCurl (realMomentum (trim k) + reflectMomentum z) i j =
      star (formalAdjointCurl (realMomentum (trim k) + z) i j) := by
  have h := curl_trim_reflection (-k) (-z) j i
  simpa only [formalAdjointCurl, Matrix.transpose_apply, realMomentum_trim_neg,
    reflectMomentum_neg, neg_add_rev, add_comm] using h

private theorem product_entry_conjugate {ι κ σ : Type*} [Fintype κ]
    (A A' : Matrix ι κ ℂ) (B B' : Matrix κ σ ℂ)
    (hA : ∀ i j, A' i j = star (A i j))
    (hB : ∀ i j, B' i j = star (B i j)) (i : ι) (j : σ) :
    (A' * B') i j = star ((A * B) i j) := by
  simp only [Matrix.mul_apply, hA, hB, star_sum, star_mul, mul_comm]

private theorem subtract_real_diagonal_conjugate {ι : Type*} [DecidableEq ι]
    (A A' : Matrix ι ι ℂ) (hA : ∀ i j, A' i j = star (A i j))
    (d : ι → ℝ) (c : ℝ) (i j : ι) :
    (A' - (c : ℂ) • Matrix.diagonal (fun i => (d i : ℂ))) i j =
      star ((A - (c : ℂ) • Matrix.diagonal (fun i => (d i : ℂ))) i j) := by
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal, hA]
  · simp [Matrix.diagonal, hA, hij]

theorem fiber_trim_reflection (material : Cell20 → ℝ) (k : Direction → ℤ)
    (z : ComplexMomentum) (i j : Electric20) :
    fiber material (realMomentum (trim k) + reflectMomentum z) i j =
      star (fiber material (realMomentum (trim k) + z) i j) := by
  have h := subtract_real_diagonal_conjugate
    (formalAdjointCurl (realMomentum (trim k) + z) * curl (realMomentum (trim k) + z))
    (formalAdjointCurl (realMomentum (trim k) + reflectMomentum z) *
      curl (realMomentum (trim k) + reflectMomentum z))
    (product_entry_conjugate _ _ _ _ (formalAdjointCurl_trim_reflection k z)
      (curl_trim_reflection k z)) (edgeAverage material) (1/64) i j
  convert h using 1 <;> norm_num [fiber, PeriodicYee.mass]

def conjugateVector {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => star (v i))

@[simp] theorem conjugateVector_apply {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (i : ι) : conjugateVector v i = star (v i) := rfl

@[simp] theorem conjugateVector_zero {ι : Type*} [Fintype ι] :
    conjugateVector (0 : EuclideanSpace ℂ ι) = 0 := by
  ext i
  simp

@[simp] theorem conjugateVector_involutive {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) : conjugateVector (conjugateVector v) = v := by
  ext i
  simp

theorem conjugateVector_ne_zero {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (hv : v ≠ 0) : conjugateVector v ≠ 0 := by
  intro h
  have hh := congrArg conjugateVector h
  apply hv
  simpa using hh

@[simp] theorem conjugateVector_smul {ι : Type*} [Fintype ι]
    (c : ℂ) (v : EuclideanSpace ℂ ι) :
    conjugateVector (c • v) = star c • conjugateVector v := by
  ext i
  simp

private theorem euclidean_operator_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A' : Matrix ι ι ℂ) (hA : ∀ i j, A' i j = star (A i j))
    (v : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A' (conjugateVector v) =
      conjugateVector (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A v) := by
  ext i
  change ∑ j, A' i j * star (v j) = star (∑ j, A i j * v j)
  simp only [hA, star_sum, star_mul, mul_comm]

theorem operator_trim_reflection (material : Cell20 → ℝ) (k : Direction → ℤ)
    (z : ComplexMomentum) (v : EuclideanSpace ℂ Electric20) :
    operator material (realMomentum (trim k) + reflectMomentum z) (conjugateVector v) =
      conjugateVector (operator material (realMomentum (trim k) + z) v) :=
  euclidean_operator_conjugate _ _ (fiber_trim_reflection material k z) v

end
end Maxwell.Spectral.ConventionalAnalytic
