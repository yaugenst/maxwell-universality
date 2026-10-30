import Maxwell.Continuum.FiniteAuxiliaryLattice
import Maxwell.Continuum.FiniteAuxiliaryCollection

/-! Distinct occupied integer sites give disjoint physical wells under
the actual integer placement map. No disjointness certificate is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Bloch CellGauge EffectiveMass PeriodicBand

theorem placement_coordinate_one (j : Fin 3) : (1 : ℝ) ≤ (placementDiagonal j : ℝ) := by
  fin_cases j <;> norm_num [placementDiagonal]

theorem placed_integer_norm_lower {L d : ℕ} (hL : 0 < (L : ℝ)) (hd : 1 ≤ d)
    {a : Bloch.Alias} (ha : a ≠ 0) :
    2*(L : ℝ) ≤ ‖latticeShift (placementCell L d a)‖ := by
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra hn
    apply ha
    funext j
    exact not_ne_iff.mp (fun hj => hn ⟨j, hj⟩)
  have hjn : (1 : ℝ) ≤ |(a j : ℝ)| := by
    have hi : 1 ≤ (a j).natAbs := Int.natAbs_pos.mpr hj
    have hi' : (1 : ℤ) ≤ ((a j).natAbs : ℤ) := by exact_mod_cast hi
    rw [Int.natCast_natAbs] at hi'
    exact_mod_cast hi'
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hc : |latticeShift (placementCell L d a) j| =
      2*(L : ℝ)*(d : ℝ)*(placementDiagonal j : ℝ)*|(a j : ℝ)| := by
    simp only [latticeShift, PiLp.smul_apply, integerVector_apply, placementCell,
      placementMatrix, Matrix.mulVec_diagonal, Int.cast_mul, Int.cast_natCast, smul_eq_mul,
      abs_mul, abs_of_nonneg (Nat.cast_nonneg L : (0 : ℝ) ≤ L),
      abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d),
      abs_of_nonneg (le_trans (by norm_num) (placement_coordinate_one j))]
    norm_num
    ring
  have hm : (1 : ℝ) ≤ ((d : ℝ)*(placementDiagonal j : ℝ))*|(a j : ℝ)| :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hd' (placement_coordinate_one j)) hjn
  calc
    _ = 2*(L : ℝ)*1 := by ring
    _ ≤ 2*(L : ℝ)*(((d : ℝ)*(placementDiagonal j : ℝ))*|(a j : ℝ)|) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = 2*(L : ℝ)*(d : ℝ)*(placementDiagonal j : ℝ)*|(a j : ℝ)| := by ring
    _ = |latticeShift (placementCell L d a) j| := hc.symm
    _ ≤ _ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (latticeShift (placementCell L d a)) j

theorem centers_disjoint {ι : Type*} {L d : ℕ} (hL : 0 < (L : ℝ)) (hd : 1 ≤ d)
    (position : ι → Bloch.Alias) (hinj : Function.Injective position) :
    Pairwise fun i j => Disjoint (Metric.ball (centers L d position i) (L : ℝ))
      (Metric.ball (centers L d position j) (L : ℝ)) := by
  intro i j hij
  apply Metric.ball_disjoint_ball
  rw [dist_eq_norm, centers_sub, ← two_mul]
  exact placed_integer_norm_lower hL hd (sub_ne_zero.mpr (hinj.ne hij))

theorem placed_collection_norm {ι : Type*} [Fintype ι] {L d : ℕ}
    (hL : 0 < (L : ℝ)) (hd : 1 ≤ d) (position : ι → Bloch.Alias)
    (hinj : Function.Injective position) :
    ‖collection (L : ℝ)⁻¹ (centers L d position)‖ ≤ 1 := by
  apply collection_norm (inv_pos.mpr hL)
  simpa only [inv_inv] using centers_disjoint hL hd position hinj

#print axioms centers_disjoint
#print axioms placed_collection_norm

end Maxwell.Continuum.FiniteAuxiliary
