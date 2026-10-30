import Maxwell.Continuum.FreeFiberNeumann

/-! Explicit finite Neumann sums with an operator-norm tail on the
whole Hilbert space. The estimates do not truncate high-frequency
longitudinal components. -/

noncomputable section

namespace Maxwell.Continuum.Calibration.Neumann

open FreeFiber

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def partialSeries (T : H →L[ℂ] H) (K : ℕ) : H →L[ℂ] H := ∑ a ∈ Finset.range K, T^a

theorem series_split (T : H →L[ℂ] H) (hT : ‖T‖ < 1) (K : ℕ) :
    FreeFiber.Neumann.series T = partialSeries T K + T^K * FreeFiber.Neumann.series T := by
  have hs : FreeFiber.Neumann.series T = 1+T*FreeFiber.Neumann.series T := by
    have he := mul_neg_geom_series T hT
    change (1-T)*FreeFiber.Neumann.series T = 1 at he
    rw [sub_mul, one_mul] at he
    exact sub_eq_iff_eq_add.mp he
  induction K with
  | zero => simp [partialSeries]
  | succ K ih =>
    calc
      _ = partialSeries T K+T^K*FreeFiber.Neumann.series T := ih
      _ = partialSeries T K+T^K*(1+T*FreeFiber.Neumann.series T) :=
        congrArg (fun S => partialSeries T K+T^K*S) hs
      _ = partialSeries T (K+1)+T^(K+1)*FreeFiber.Neumann.series T := by
        rw [partialSeries, partialSeries, Finset.sum_range_succ, pow_succ]
        noncomm_ring

theorem series_tail_norm (T : H →L[ℂ] H) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hT : ‖T‖ ≤ r) (K : ℕ) :
    ‖FreeFiber.Neumann.series T-partialSeries T K‖ ≤ r^K*(1-r)⁻¹ := by
  have ht := hT.trans_lt hr
  have he : FreeFiber.Neumann.series T-partialSeries T K = T^K*FreeFiber.Neumann.series T := by
    exact sub_eq_iff_eq_add.mpr ((series_split T ht K).trans (add_comm _ _))
  rw [he]
  have hden : 0 < 1-‖T‖ := by linarith
  have hinv : (1-‖T‖)⁻¹ ≤ (1-r)⁻¹ :=
    (inv_le_inv₀ hden (by linarith)).mpr (by linarith)
  have hp : ∀ k : ℕ, ‖T^k‖ ≤ ‖T‖^k := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, pow_zero]
      change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg T))
  exact (norm_mul_le _ _).trans (mul_le_mul
    ((hp K).trans (pow_le_pow_left₀ (norm_nonneg _) hT K))
    ((FreeFiber.Neumann.series_norm_le T ht).trans hinv) (norm_nonneg _) (pow_nonneg hr0 K))

def inverseApprox (R B : H →L[ℂ] H) (K : ℕ) : H →L[ℂ] H := R*partialSeries (-(B*R)) K

theorem inverseApprox_error (R B : H →L[ℂ] H) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hBR : ‖B*R‖ ≤ r) (K : ℕ) :
    ‖R*FreeFiber.Neumann.series (-(B*R))-inverseApprox R B K‖ ≤
      ‖R‖*r^K*(1-r)⁻¹ := by
  rw [inverseApprox, ← mul_sub]
  exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left
    (series_tail_norm (-(B*R)) hr0 hr (by simpa only [norm_neg] using hBR) K)
    (norm_nonneg R)).trans_eq (by ring))

#print axioms inverseApprox_error

end Maxwell.Continuum.Calibration.Neumann
