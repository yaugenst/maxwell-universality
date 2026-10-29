import Maxwell.Spectral.YeeTaylorRemainder
import Maxwell.Spectral.Perturbation

/-!
# Actual primitive Yee displacement and a center-count transfer

This global operator-norm bound is deliberately separate from the stronger
independent interval-inertia certificate used for the full paper neighborhood.
At radius `1/20` its bound is `1/9`, so a center complement gap of `11/2000`
alone does not certify inertia on that whole ball.
-/

namespace Maxwell.Spectral.YeeDisplacement

open Maxwell.Spectral.PeriodicYee
open Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.YeeTaylor
open Maxwell.Spectral.YeeTaylorRemainder

noncomputable section

/-- The one-degree majorant ratio after positive degree. -/
theorem taylorCoefficientMajorant_successor (j : ℕ) (hj : 1 ≤ j) :
    taylorCoefficientMajorant (j + 1) ≤
      (11 / 70 : ℝ) * taylorCoefficientMajorant j := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hden : 2 * (j.factorial : ℝ) ≤ ((j + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hnum : (4 * (2 : ℝ) ^ (j + 1) + 6) * (11 / 70) ^ (j + 1) ≤
      2 * (4 * (2 : ℝ) ^ j + 6) * (11 / 70) ^ j * (11 / 70) := by
    rw [pow_succ, pow_succ]
    have hn : 0 ≤ (11 / 70 : ℝ) ^ j := by positivity
    nlinarith only [hn]
  unfold taylorCoefficientMajorant
  calc
    _ ≤ (2 * (4 * (2 : ℝ) ^ j + 6) * (11 / 70) ^ j * (11 / 70)) /
        (2 * (j.factorial : ℝ)) :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = _ := by ring

/-- The entire positive-degree scalar Taylor majorant is bounded by a
geometric series, including zero radius. -/
theorem positive_taylor_majorant (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20) :
    Summable (fun n : ℕ => taylorCoefficientMajorant (n + 1) * r ^ (n + 1)) ∧
      (∑' n : ℕ, taylorCoefficientMajorant (n + 1) * r ^ (n + 1)) ≤
        (20 / 9) * r := by
  let f := fun n : ℕ => taylorCoefficientMajorant (n + 1) * r ^ (n + 1)
  have hf0 (n : ℕ) : 0 ≤ f n :=
    mul_nonneg (taylorCoefficientMajorant_nonnegative _) (pow_nonneg hr0 _)
  have hstep (n : ℕ) : f (n + 1) ≤ f n * (1 / 100) := by
    have hcoeff := taylorCoefficientMajorant_successor (n + 1) (by omega)
    have hc := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hr0 (n + 1 + 1))
    change taylorCoefficientMajorant (n + 1 + 1) * r ^ (n + 1 + 1) ≤ _ at hc
    have hscale : (11 / 70 : ℝ) * r ≤ 1 / 100 := by linarith
    calc
      f (n + 1) ≤ ((11 / 70) * taylorCoefficientMajorant (n + 1)) *
          r ^ (n + 1 + 1) := hc
      _ = f n * ((11 / 70) * r) := by dsimp [f]; rw [pow_succ]; ring
      _ ≤ f n * (1 / 100) := mul_le_mul_of_nonneg_left hscale (hf0 n)
  have hbound (n : ℕ) : f n ≤ f 0 * (1 / 100 : ℝ) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        f (n + 1) ≤ f n * (1 / 100) := hstep n
        _ ≤ (f 0 * (1 / 100 : ℝ) ^ n) * (1 / 100) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  have hgeom := (hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : (1 / 100 : ℝ) < 1)).mul_left (f 0)
  have hs : Summable f := Summable.of_nonneg_of_le hf0 hbound hgeom.summable
  refine ⟨hs, ?_⟩
  have ht := hs.tsum_le_tsum hbound hgeom.summable
  rw [hgeom.tsum_eq] at ht
  convert ht using 1
  norm_num [f, taylorCoefficientMajorant, Nat.factorial]
  ring

/-- At zero displacement the centered matrix is the actual primitive fiber. -/
theorem centeredFiber_zero (material : Cell20 → ℝ) (k : Momentum) :
    centeredFiber material k 0 = PrimitiveYee.fiber material k := by
  have hd : centeredDifference k 0 = PrimitiveYee.difference k := by
    funext j
    simp [centeredDifference, difference_eq_shift_sub_one]
  simp only [centeredFiber, centeredCurl, hd]
  rfl

/-- The degree-zero CLM coefficient is this same actual center operator. -/
theorem shiftedOperatorCoefficient_zero (k : Translation) (q : Momentum) :
    shiftedOperatorCoefficient Concrete.material (timeReversalMomentum k) q 0 0 =
      centeredOperator k 0 := by
  simp only [shiftedOperatorCoefficient, YeeTaylor.shiftedFiberCoefficient_zero,
    Complex.ofReal_zero, zero_smul, sub_zero, centeredOperator, centeredFiber_zero]
  rfl

/-- Summing the positive-degree coefficients bounds the difference of the
actual frozen-material centered primitive operators. -/
theorem centeredOperator_displacement (k : Translation) (q : Momentum)
    (hr : radius q ≤ 1 / 20) :
    ‖centeredOperator k q - centeredOperator k 0‖ ≤ (20 / 9) * radius q := by
  have hs := shiftedOperatorCoefficient_hasSum Concrete.material
    (timeReversalMomentum k) q 0
  have hs' := (hasSum_nat_add_iff' 1).mpr hs
  have hcenter : shiftedCenteredOperator Concrete.material
      (timeReversalMomentum k) q 0 = centeredOperator k q := by
    simp only [shiftedCenteredOperator, Complex.ofReal_zero, zero_smul, sub_zero,
      centeredOperator]
    rfl
  simp only [Finset.sum_range_one, shiftedOperatorCoefficient_zero, hcenter] at hs'
  obtain ⟨hmaj, hbound⟩ := positive_taylor_majorant (radius q) (radius_nonneg q) hr
  exact (hs'.norm_le_of_bounded hmaj.hasSum (fun n =>
    shiftedOperatorCoefficient_norm_le Concrete.material
      (timeReversalMomentum k) q 0 (n + 1) (by omega))).trans hbound

/-- Every ordered actual Yee eigenvalue moves by at most the proved norm
bound. This statement makes no center spectral-isolation assumption. -/
theorem centeredOperator_eigenvalue_displacement (k : Translation) (q : Momentum)
    (hr : radius q ≤ 1 / 20)
    (i : Fin (Module.finrank ℂ (EuclideanSpace ℂ Electric))) :
    |(centeredOperator_symmetric k q).eigenvalues rfl i -
      (centeredOperator_symmetric k 0).eigenvalues rfl i| ≤ (20 / 9) * radius q :=
  eigenvalues_abs_sub_le_of_norm_sub_le (centeredOperator k q) (centeredOperator k 0)
    (centeredOperator_symmetric k q) (centeredOperator_symmetric k 0)
    ((20 / 9) * radius q) (centeredOperator_displacement k q hr) i

/-- A sufficient center certificate for any displaced interval count. The
center interval is explicitly widened by the proved actual displacement. -/
theorem centeredOperator_interval_count_le (k : Translation) (q : Momentum)
    (hr : radius q ≤ 1 / 20) (a b : ℝ) :
    (Finset.univ.filter fun i => a < (centeredOperator_symmetric k q).eigenvalues rfl i ∧
      (centeredOperator_symmetric k q).eigenvalues rfl i < b).card ≤
    (Finset.univ.filter fun i => a - (20 / 9) * radius q <
      (centeredOperator_symmetric k 0).eigenvalues rfl i ∧
      (centeredOperator_symmetric k 0).eigenvalues rfl i < b + (20 / 9) * radius q).card := by
  apply card_eigenvalues_mem_Ioo_le_of_norm_sub_le
    (centeredOperator k 0) (centeredOperator k q)
    (centeredOperator_symmetric k 0) (centeredOperator_symmetric k q)
  simpa only [norm_sub_rev] using centeredOperator_displacement k q hr

/-- In particular, an enlarged-center-band count of at most two yields the
actual displaced inertia premise used by the local polynomial theorem. -/
theorem centeredOperator_local_inertia (k : Translation) (q : Momentum)
    (hr : radius q ≤ 1 / 20)
    (hcenter : (Finset.univ.filter fun i => -(20 / 9) * radius q <
      (centeredOperator_symmetric k 0).eigenvalues rfl i ∧
      (centeredOperator_symmetric k 0).eigenvalues rfl i <
        7 / 256 + (20 / 9) * radius q).card ≤ 2) :
    (Finset.univ.filter fun i => 0 < (centeredOperator_symmetric k q).eigenvalues rfl i ∧
      (centeredOperator_symmetric k q).eigenvalues rfl i < 7 / 256).card ≤ 2 := by
  have hc := centeredOperator_interval_count_le k q hr 0 (7 / 256)
  simp only [zero_sub] at hc
  exact hc.trans (by simpa only [neg_mul] using hcenter)

end
end Maxwell.Spectral.YeeDisplacement
