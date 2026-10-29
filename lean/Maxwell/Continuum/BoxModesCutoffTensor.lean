import Maxwell.Continuum.BoxModesCutoff
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Tensor cutoffs and their literal Cartesian derivatives. -/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open Filter MeasureTheory
open scoped Topology ContDiff BigOperators

theorem partial_separated_product (f : Fin 3 → ℝ → ℝ)
    (hf : ∀ k, Differentiable ℝ (f k)) (j : Fin 3) (x : Point) :
    partialDeriv (fun y => ∏ k, f k (y k)) j x =
      deriv (f j) (x j) * ∏ k ∈ Finset.univ.erase j, f k (x k) := by
  have hd (k : Fin 3) : HasFDerivAt (fun y : Point => f k (y k))
      (deriv (f k) (x k) • (PiLp.proj 2 (fun _ : Fin 3 => ℝ) k)) x :=
    ((hf k).differentiableAt.hasDerivAt).comp_hasFDerivAt x
      (show HasFDerivAt (fun y : Point => y k)
        (PiLp.proj 2 (fun _ : Fin 3 => ℝ) k) x from
        (PiLp.proj 2 (fun _ : Fin 3 => ℝ) k : Point →L[ℝ] ℝ).hasFDerivAt)
  have hp := HasFDerivAt.finsetProd (u := Finset.univ) (fun k _ => hd k)
  unfold partialDeriv
  rw [hp.fderiv]
  simp [direction, PiLp.single_apply, eq_comm, mul_comm]

theorem contDiff_coordinateMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c j : Fin 3) :
    ContDiff ℝ ∞ (coordinateMode N ν c j) := by
  unfold coordinateMode
  split_ifs
  · exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (ν j : ℝ) * Real.pi / N j)).mul
      contDiff_id).cos
  · exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (ν j : ℝ) * Real.pi / N j)).mul
      contDiff_id).sin

theorem abs_coordinateMode_le_one (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c j : Fin 3)
    (x : ℝ) : |coordinateMode N ν c j x| ≤ 1 := by
  unfold coordinateMode intervalCos intervalSin
  split_ifs
  · exact Real.abs_cos_le_one _
  · exact Real.abs_sin_le_one _

theorem deriv_coordinateMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c j : Fin 3) (x : ℝ) :
    deriv (coordinateMode N ν c j) x =
      if j = c then -((ν j : ℝ) * Real.pi / N j) * intervalSin (N j) (ν j) x
      else ((ν j : ℝ) * Real.pi / N j) * intervalCos (N j) (ν j) x := by
  by_cases hj : j = c
  · have he : coordinateMode N ν c j =
        fun t => Real.cos ((ν j : ℝ) * Real.pi / N j * t) := by
      funext t
      simp only [coordinateMode, ite_eq_left hj, intervalCos]
    rw [he, ite_eq_left hj]
    have h := (((hasDerivAt_id x).const_mul ((ν j : ℝ) * Real.pi / N j)).cos).deriv
    convert h using 1 <;> dsimp [intervalSin, intervalCos, id]
    ring
  · have he : coordinateMode N ν c j =
        fun t => Real.sin ((ν j : ℝ) * Real.pi / N j * t) := by
      funext t
      simp only [coordinateMode, ite_eq_right hj, intervalSin]
    rw [he, ite_eq_right hj]
    have h := (((hasDerivAt_id x).const_mul ((ν j : ℝ) * Real.pi / N j)).sin).deriv
    convert h using 1 <;> dsimp [intervalSin, intervalCos, id]
    ring

theorem abs_deriv_coordinateMode_le (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c j : Fin 3)
    (x : ℝ) : |deriv (coordinateMode N ν c j) x| ≤ |(ν j : ℝ) * Real.pi / N j| := by
  rw [deriv_coordinateMode]
  split_ifs
  · rw [abs_mul, abs_neg]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans_eq (mul_one _)
  · rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _)

def cutoffCoordinateMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3)
    (δ : ℝ) (j : Fin 3) (x : ℝ) : ℝ :=
  intervalCutoff (N j) δ x * coordinateMode N ν c j x

def cutoffScalarMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ) (c : Fin 3)
    (δ : ℝ) (x : Point) : ℝ := ∏ j, cutoffCoordinateMode N ν c δ j (x j)

theorem contDiff_cutoffCoordinateMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c : Fin 3) (δ : ℝ) (j : Fin 3) : ContDiff ℝ ∞ (cutoffCoordinateMode N ν c δ j) :=
  (contDiff_intervalCutoff (N j) δ).mul (contDiff_coordinateMode N ν c j)

theorem contDiff_cutoffScalarMode (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c : Fin 3) (δ : ℝ) : ContDiff ℝ ∞ (cutoffScalarMode N ν c δ) := by
  apply contDiff_prod
  intro j _
  exact (contDiff_cutoffCoordinateMode N ν c δ j).comp
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Point →L[ℝ] ℝ).contDiff

theorem abs_cutoffCoordinateMode_le_one (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c : Fin 3) (δ : ℝ) (j : Fin 3) (x : ℝ) :
    |cutoffCoordinateMode N ν c δ j x| ≤ 1 := by
  rw [cutoffCoordinateMode, abs_mul, abs_of_nonneg (intervalCutoff_nonneg _ _ _)]
  calc
    intervalCutoff (N j) δ x * |coordinateMode N ν c j x| ≤ 1 * 1 :=
      mul_le_mul (intervalCutoff_le_one _ _ _) (abs_coordinateMode_le_one N ν c j x)
        (abs_nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem abs_cutoffScalarMode_le_one (N : Fin 3 → ℝ) (ν : Fin 3 → ℤ)
    (c : Fin 3) (δ : ℝ) (x : Point) : |cutoffScalarMode N ν c δ x| ≤ 1 := by
  rw [cutoffScalarMode, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
    (fun j _ => abs_cutoffCoordinateMode_le_one N ν c δ j (x j))

theorem abs_deriv_cutoffCoordinateMode_le (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c j : Fin 3) (hj : j ≠ c)
    (C : ℝ) (hC : 0 ≤ C) (hD : ∀ y, |deriv Real.smoothTransition y| ≤ C)
    {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |deriv (cutoffCoordinateMode N ν c δ j) x| ≤
      (4 * C + 1) * |(ν j : ℝ) * Real.pi / N j| := by
  have hc := (contDiff_intervalCutoff (N j) δ).differentiable (by simp)
  have hm := (contDiff_coordinateMode N ν c j).differentiable (by simp)
  have hd := (hc.differentiableAt (x := x)).hasDerivAt.mul
    (hm.differentiableAt (x := x)).hasDerivAt
  change HasDerivAt (cutoffCoordinateMode N ν c δ j) _ x at hd
  rw [hd.deriv]
  have hfirst : |deriv (intervalCutoff (N j) δ) x * coordinateMode N ν c j x| ≤
      4 * C * |(ν j : ℝ) * Real.pi / N j| := by
    simpa only [coordinateMode, ite_eq_right hj] using
      intervalCutoff_deriv_sin_bound (N j) (hN j) (ν j) C hC hD hδ x
  have hsecond : |intervalCutoff (N j) δ x * deriv (coordinateMode N ν c j) x| ≤
      |(ν j : ℝ) * Real.pi / N j| := by
    rw [abs_mul, abs_of_nonneg (intervalCutoff_nonneg _ _ _)]
    exact (mul_le_mul (intervalCutoff_le_one _ _ _) (abs_deriv_coordinateMode_le N ν c j x)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  exact (abs_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

/-- The tangential partial derivatives needed by curl have a width-independent
bound. No derivative in the component's normal direction is required. -/
theorem abs_partial_cutoffScalarMode_le (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℤ) (c j : Fin 3) (hj : j ≠ c)
    (C : ℝ) (hC : 0 ≤ C) (hD : ∀ y, |deriv Real.smoothTransition y| ≤ C)
    {δ : ℝ} (hδ : 0 < δ) (x : Point) :
    |partialDeriv (cutoffScalarMode N ν c δ) j x| ≤
      (4 * C + 1) * |(ν j : ℝ) * Real.pi / N j| := by
  change |partialDeriv (fun y => ∏ k, cutoffCoordinateMode N ν c δ k (y k)) j x| ≤ _
  rw [partial_separated_product _
    (fun k => (contDiff_cutoffCoordinateMode N ν c δ k).differentiable (by simp)), abs_mul]
  have hprod : |∏ k ∈ Finset.univ.erase j, cutoffCoordinateMode N ν c δ k (x k)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
      (fun k _ => abs_cutoffCoordinateMode_le_one N ν c δ k (x k))
  exact (mul_le_mul (abs_deriv_cutoffCoordinateMode_le N hN ν c j hj C hC hD hδ (x j))
    hprod (abs_nonneg _) (by positivity)).trans_eq (mul_one _)

#print axioms abs_partial_cutoffScalarMode_le

end Maxwell.Continuum.BoxModes
