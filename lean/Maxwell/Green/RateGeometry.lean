import Maxwell.Green.Whitening
import Maxwell.Green.RelativeTaylor
import Maxwell.Green.BlockContour
import Maxwell.Green.Rates

/-! The same Hessian metric controls the global lattice decay and each
axial support exponent. The strict margin is retained after integer rounding. -/

noncomputable section

namespace Maxwell.Green

open Matrix Set
open scoped InnerProductSpace Matrix.Norms.L2Operator

theorem coordinate_abs_sum_le_sqrt_three_norm (x : Vec3) :
    ∑ j : Fin 3, |x j| ≤ Real.sqrt 3 * ‖x‖ := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin 3 => (1 : ℝ)) (fun j => |x j|)
  have hn : ‖x‖ ^ 2 = ∑ j : Fin 3, (x j) ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  have hs : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sq_abs] at hc
  have hnonneg : 0 ≤ Real.sqrt 3 * ‖x‖ := by positivity
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hnonneg).mp
  rw [mul_pow, hs, hn]
  exact hc

theorem roundedPlacement_integerMomentum (M : ℕ) (Q : Mat3) (n : Fin 3 → ℤ) :
    integerMomentum (roundedPlacement M Q *ᵥ n) =
      matrixAction (roundedPlacementReal M Q) (integerMomentum n) := by
  ext i
  simp [integerMomentum, matrixAction, Matrix.mulVec, dotProduct, roundedPlacementReal]

theorem roundedPlacement_l1_distortion (M : ℕ) (Q P : Mat3)
    (hPQ : P * Q = 1) (hM : 3 * ‖P‖ ≤ (1 / 100 : ℝ) * (M : ℝ))
    (n : Fin 3 → ℤ) :
    (M : ℝ) * (1 - (1 : ℝ) / 100) / Real.sqrt 3 *
      (∑ j : Fin 3, |(n j : ℝ)|) ≤
      ‖matrixAction P (integerMomentum (roundedPlacement M Q *ᵥ n))‖ := by
  have hd := (roundedPlacement_relative_distortion M Q P hPQ (1 / 100) hM
    (integerMomentum n)).1
  have hc := coordinate_abs_sum_le_sqrt_three_norm (integerMomentum n)
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hcn : (∑ j : Fin 3, |(n j : ℝ)|) / Real.sqrt 3 ≤ ‖integerMomentum n‖ := by
    apply (div_le_iff₀ hs).mpr
    change (∑ j : Fin 3, |(n j : ℝ)|) ≤ Real.sqrt 3 * ‖integerMomentum n‖ at hc
    exact hc.trans_eq (mul_comm _ _)
  have hnonneg : 0 ≤ (M : ℝ) * (1 - (1 : ℝ) / 100) := by positivity
  calc
    _ = ((M : ℝ) * (1 - (1 : ℝ) / 100)) *
        ((∑ j : Fin 3, |(n j : ℝ)|) / Real.sqrt 3) := by ring
    _ ≤ ((M : ℝ) * (1 - (1 : ℝ) / 100)) * ‖integerMomentum n‖ :=
      mul_le_mul_of_nonneg_left hcn hnonneg
    _ ≤ ‖matrixAction (P * roundedPlacementReal M Q) (integerMomentum n)‖ := hd
    _ = _ := by rw [roundedPlacement_integerMomentum]; simp only [matrixAction, map_mul,
      mul_apply_eq_comp]

/-- All metric and integer-placement witnesses are constructed from the
actual symmetric positive Hessian. -/
theorem exists_whitened_integer_placement
    (B : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x)
    (hpos : ∀ x : Vec3, x ≠ 0 → 0 < B x x) :
    ∃ (Q P : Mat3) (M : ℕ), 0 < M ∧ P * Q = 1 ∧ Q * P = 1 ∧
      P.IsHermitian ∧
      (∀ x y : Vec3, inner ℝ (matrixAction P x) y = inner ℝ x (matrixAction P y)) ∧
      (∀ x : Vec3, ‖matrixAction Q x‖ ^ 2 = B x x) ∧
      IsUnit (roundedPlacementReal M Q) ∧
      (∀ x : Vec3,
        (M : ℝ) * (1 - (1 : ℝ) / 100) * ‖x‖ ≤
          ‖matrixAction (P * roundedPlacementReal M Q) x‖ ∧
        ‖matrixAction (P * roundedPlacementReal M Q) x‖ ≤
          (M : ℝ) * (1 + (1 : ℝ) / 100) * ‖x‖) ∧
      ∀ n : Fin 3 → ℤ,
        (M : ℝ) * (1 - (1 : ℝ) / 100) / Real.sqrt 3 *
          (∑ j : Fin 3, |(n j : ℝ)|) ≤
          ‖matrixAction P (integerMomentum (roundedPlacement M Q *ᵥ n))‖ := by
  obtain ⟨Q, P, hPQ, hQP, hP, hsym, hmetric⟩ := exists_bilinear_hessian_whitening B hB hpos
  obtain ⟨M, hMpos, hM⟩ := exists_roundedPlacement_scale P (1 / 100) (by norm_num)
  have hM' : 3 * ‖P‖ < (M : ℝ) := by
    have hp : 0 < (M : ℝ) := by exact_mod_cast hMpos
    linarith
  exact ⟨Q, P, M, hMpos, hPQ, hQP, hP, hsym, hmetric,
    roundedPlacement_isUnit M Q P hPQ hM',
    roundedPlacement_relative_distortion M Q P hPQ (1 / 100) hM.le,
    roundedPlacement_l1_distortion M Q P hPQ hM.le⟩

/-- The relative Hessian comparison places a strictly smaller ellipsoid
inside the physical level, uniformly in every direction. -/
theorem relative_level_inner_ellipsoid {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (Q : E →L[ℝ] E) (ξ : ℝ) (hξ : 0 < ξ) (β : E)
    (hupper : F β ≤ (1 + (1 : ℝ) / 100) * ‖Q β‖ ^ 2 / 2)
    (hβ : ‖Q β‖ ≤ (1 - (1 : ℝ) / 100) * Real.sqrt (2 * ξ)) : F β < ξ := by
  have hs : Real.sqrt (2 * ξ) ^ 2 = 2 * ξ := Real.sq_sqrt (by positivity)
  have ht : 0 ≤ (1 - (1 : ℝ) / 100) * Real.sqrt (2 * ξ) := by positivity
  have hsq := sq_le_sq₀ (norm_nonneg (Q β)) ht |>.mpr hβ
  nlinarith

/-- Every point on the actual level has the matching outer metric bound. -/
theorem relative_level_outer_ellipsoid {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (Q : E →L[ℝ] E) (ξ : ℝ) (hξ : 0 < ξ) (β : E)
    (hlower : (1 - (1 : ℝ) / 100) * ‖Q β‖ ^ 2 / 2 ≤ F β)
    (hlevel : F β ≤ ξ) : ‖Q β‖ ≤ (1 + (1 : ℝ) / 100) * Real.sqrt (2 * ξ) := by
  have hs : Real.sqrt (2 * ξ) ^ 2 = 2 * ξ := Real.sq_sqrt (by positivity)
  have ht : 0 ≤ (1 + (1 : ℝ) / 100) * Real.sqrt (2 * ξ) := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) ht).mp
  nlinarith

end Maxwell.Green
