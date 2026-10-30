import Maxwell.Continuum.CalibrationBumpDegree
import Maxwell.Continuum.PeriodicSamplingCoefficientNorm

/-! A precision-requested, finite rational Fourier approximation to
the actual torus well root, with no numerical-oracle premise. -/

namespace Maxwell.Continuum.Calibration

open PeriodicSampling UnitAddTorus Maxwell.Certificate

noncomputable def rationalRootPolynomialContinuous (grid D P : ℕ) [NeZero grid] (s : ℚ) :
    C(UnitAddTorus (Fin 3), ℂ) :=
  ⟨rationalRootPolynomial grid D P s, by
    unfold rationalRootPolynomial Product.polynomial
    apply continuous_finsetSum
    intro n _
    exact (mFourier n).continuous.mul continuous_const⟩

theorem rationalRootPolynomialContinuous_apply (grid D P : ℕ) [NeZero grid] (s : ℚ)
    (x : UnitAddTorus (Fin 3)) :
    rationalRootPolynomialContinuous grid D P s x = rationalRootPolynomial grid D P s x := rfl

def rootSamplingGrid (s : ℚ) (N ell : ℕ) : ℕ := 2*rootDegree s N ell+1

instance rootSamplingGrid_neZero (s : ℚ) (N ell : ℕ) : NeZero (rootSamplingGrid s N ell) :=
  ⟨by unfold rootSamplingGrid; omega⟩

def rootSamplingBits (s : ℚ) (N ell : ℕ) : ℕ := N+rootCoefficientGuard (rootDegree s N ell)+8

def computedRootCoefficient (s : ℚ) (N ell : ℕ) (n : Fin 3 → ℤ) : ComplexRectangle :=
  rationalRootCoefficient (rootSamplingGrid s N ell) s (rootSamplingBits s N ell) n

noncomputable def computedRootPolynomial (s : ℚ) (N ell : ℕ) : C(UnitAddTorus (Fin 3), ℂ) :=
  rationalRootPolynomialContinuous (rootSamplingGrid s N ell) (rootDegree s N ell)
    (rootSamplingBits s N ell) s

theorem computedRootPolynomial_apply (s : ℚ) (N ell : ℕ) (x : UnitAddTorus (Fin 3)) :
    computedRootPolynomial s N ell x =
      rationalRootPolynomial (rootSamplingGrid s N ell) (rootDegree s N ell)
        (rootSamplingBits s N ell) s x := by
  exact rationalRootPolynomialContinuous_apply (rootSamplingGrid s N ell) (rootDegree s N ell)
    (rootSamplingBits s N ell) s x

theorem computedRootPolynomial_error (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell) (x : UnitAddTorus (Fin 3)) :
    ‖rootTorus s hs x-computedRootPolynomial s N ell x‖ ≤ (1/2 : ℝ)^N := by
  rw [computedRootPolynomial_apply]
  exact rationalRootPolynomial_requested (rootSamplingGrid s N ell)
    (rootDegree s N ell) (rootDegree s N ell) N ell s hs
    (by unfold rootSamplingGrid; omega) (rootDegree_pos s hs N ell) (by omega) hlog
    (rootDegree_admissible s hs N ell hlog) x

theorem computedRootPolynomial_norm_error (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell) :
    ‖rootTorus s hs-computedRootPolynomial s N ell‖ ≤ (1/2 : ℝ)^N := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  exact computedRootPolynomial_error s hs N ell hlog

theorem computedRootPolynomial_norm (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell) : ‖computedRootPolynomial s N ell‖ ≤ 2 := by
  have he := computedRootPolynomial_norm_error s hs N ell hlog
  have hr : ‖rootTorus s hs‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).mpr (rootTorus_norm_le_one s hs)
  have ht := norm_sub_le_norm_sub_add_norm_sub (computedRootPolynomial s N ell) (rootTorus s hs) 0
  simp only [sub_zero] at ht
  rw [norm_sub_rev] at ht
  have hp : (1/2 : ℝ)^N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

theorem computedRootCoefficient_norm (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ) (n : Fin 3 → ℤ) :
    ‖rectangleCenter (computedRootCoefficient s N ell n)‖ ≤ 9 := by
  let M := rootSamplingGrid s N ell
  let P := rootSamplingBits s N ell
  let k := Product.frequency M n
  let f : (Fin 3 → ZMod M) → ℂ := fun j =>
    rootTorus s hs (fun i => ((((j i).val : ℝ)/M : ℝ) : UnitAddCircle))
  have he := rationalRootCoefficient_error M s hs P n
  have hn := Product.coefficient_norm_le M f k 1 (fun j => rootTorus_norm_le_one s hs _)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (rectangleCenter (computedRootCoefficient s N ell n)) (Product.coefficient M f k) 0
  simp only [sub_zero] at ht
  rw [norm_sub_rev] at ht
  have hp : (1/2 : ℝ)^P ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  change ‖Product.coefficient M f k-rectangleCenter (computedRootCoefficient s N ell n)‖ ≤ _ at he
  linarith

theorem computedRootCoefficient_l1 (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ) :
    (∑ n ∈ Product.frequencyCube (rootDegree s N ell),
      ‖rectangleCenter (computedRootCoefficient s N ell n)‖) ≤
        9*((2*rootDegree s N ell+1 : ℕ) : ℝ)^3 := by
  calc
    _ ≤ ∑ _n ∈ Product.frequencyCube (rootDegree s N ell), (9 : ℝ) :=
      Finset.sum_le_sum (fun n _ => computedRootCoefficient_norm s hs N ell n)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Product.frequencyCube_card, Nat.cast_pow]; ring

#print axioms computedRootPolynomial_error
#print axioms computedRootCoefficient_l1

end Maxwell.Continuum.Calibration
