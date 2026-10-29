import Maxwell.Composition.ModeDecoder

/-! The finite calibrated decoder uses the total sampled support count in its
precision budget. No dimension factor is omitted or supplied by a premise. -/
noncomputable section
namespace Maxwell.Composition
open scoped BigOperators

theorem sqrt_nat_le (n : ℕ) : Real.sqrt (n : ℝ) ≤ n := by
  cases n with
  | zero => simp
  | succ n =>
    apply (Real.sqrt_le_iff).mpr
    have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact ⟨by positivity, by nlinarith⟩

theorem rational_mode_l1_le {k : ℕ} (qhat : Fin k → ℚ)
    (hq : ‖WithLp.toLp 2 (fun j => (qhat j : ℝ))‖ ≤ 2) :
    ∑ j, |(qhat j : ℝ)| ≤ 2 * k := by
  calc
    _ ≤ ∑ _j : Fin k, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      have hj := PiLp.norm_apply_le (WithLp.toLp 2 (fun j => (qhat j : ℝ))) j
      have ha : |(qhat j : ℝ)| ≤ ‖WithLp.toLp 2 (fun j => (qhat j : ℝ))‖ := by
        simpa only [WithLp.ofLp_toLp, Real.norm_eq_abs] using hj
      exact ha.trans hq
    _ = _ := by simp; ring

theorem localModeDecoder_row_count_bound {ι : Type*} {m k : ℕ}
    (pick : Fin m × Fin k → ι) (qhat : Fin k → ℚ) (v : Fin m → ℚ)
    (format : Target.FixedPointFormat) (vmax : ℝ) (hvmax : 0 ≤ vmax)
    (hv : ∀ i, |(v i : ℝ)| ≤ vmax)
    (hq : ‖WithLp.toLp 2 (fun j => (qhat j : ℝ))‖ ≤ 2) (i : Fin m) :
    ∑ j ∈ (localModeDecoder pick qhat v format).support i,
      |((localModeDecoder pick qhat v format).weight i j : ℝ)| ≤ 2 * vmax * k := by
  rw [localModeDecoder_row_l1]
  have h := mul_le_mul (hv i) (rational_mode_l1_le qhat hq)
    (Finset.sum_nonneg fun j _ => abs_nonneg _) hvmax
  nlinarith

/-- Actual fixed-width samples, the stored rational coefficients and the
complete number of sampled coordinates imply the finite readout budget. -/
theorem localModeDecoder_error_count_bound {ι : Type*} {m k : ℕ}
    (pick : Fin m × Fin k → ι) (qhat : Fin k → ℚ) (v : Fin m → ℚ)
    (format : Target.FixedPointFormat) (vmax : ℝ) (hvmax : 0 ≤ vmax)
    (hv : ∀ i, |(v i : ℝ)| ≤ vmax)
    (hq : ‖WithLp.toLp 2 (fun j => (qhat j : ℝ))‖ ≤ 2)
    (w : (localModeDecoder pick qhat v format).Messages) (y : ι → ℝ)
    (hw : (localModeDecoder pick qhat v format).Accurate w y) :
    ‖WithLp.toLp 2 (fun i => ((localModeDecoder pick qhat v format).decode w i : ℝ)) -
      WithLp.toLp 2 ((localModeDecoder pick qhat v format).ideal y)‖ ≤
      2 * vmax * (m * k : ℕ) / (2 : ℝ) ^ format.fractionalBits := by
  have h := (localModeDecoder pick qhat v format).decode_euclidean_error_le
    w y hw (2 * vmax * k) (by positivity)
    (localModeDecoder_row_count_bound pick qhat v format vmax hvmax hv hq)
  calc
    _ ≤ Real.sqrt m * ((2 * vmax * k) / (2 : ℝ) ^ format.fractionalBits) := h
    _ ≤ (m : ℝ) * ((2 * vmax * k) / (2 : ℝ) ^ format.fractionalBits) :=
      mul_le_mul_of_nonneg_right (sqrt_nat_le m) (by positivity)
    _ = _ := by push_cast; ring

/-- The literal coordinate precision chosen by the parameter program is
sufficient for the stronger full-vector error bound `eps/4096`. -/
theorem localModeDecoder_error_precision {ι : Type*} {m k : ℕ}
    (pick : Fin m × Fin k → ι) (qhat : Fin k → ℚ) (v : Fin m → ℚ)
    (format : Target.FixedPointFormat) (vmax eps : ℝ) (hvmax : 0 ≤ vmax)
    (hv : ∀ i, |(v i : ℝ)| ≤ vmax)
    (hq : ‖WithLp.toLp 2 (fun j => (qhat j : ℝ))‖ ≤ 2)
    (hprecision : 2 * vmax * (m * k : ℕ) / (2 : ℝ)^format.fractionalBits ≤ eps / 4096)
    (w : (localModeDecoder pick qhat v format).Messages) (y : ι → ℝ)
    (hw : (localModeDecoder pick qhat v format).Accurate w y) :
    ‖WithLp.toLp 2 (fun i => ((localModeDecoder pick qhat v format).decode w i : ℝ)) -
      WithLp.toLp 2 ((localModeDecoder pick qhat v format).ideal y)‖ ≤ eps / 4096 :=
  (localModeDecoder_error_count_bound pick qhat v format vmax hvmax hv hq w y hw).trans hprecision

/-- Actual incident-cell weights make the uncalibrated local readout mode
contractive. The local vector is the same weighted mode used by assembly. -/
theorem weightedLocalMode_norm_le {κ : Type*} [Fintype κ]
    (w : κ → ℚ) (hw : ∀ j, 0 ≤ (w j : ℝ) ∧ (w j : ℝ) ≤ 1)
    (u : EuclideanSpace ℝ κ) : ‖weightedLocalMode w u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro j _
  change (Real.sqrt (w j : ℝ) * u j)^2 ≤ (u j)^2
  rw [mul_pow, Real.sq_sqrt (hw j).1]
  exact (mul_le_mul_of_nonneg_right (hw j).2 (sq_nonneg _)).trans_eq (one_mul _)

theorem calibrated_mode_norm_le_two {κ : Type*} [Fintype κ]
    (w : κ → ℚ) (hw : ∀ j, 0 ≤ (w j : ℝ) ∧ (w j : ℝ) ≤ 1)
    (u : EuclideanSpace ℝ κ) (hu : ‖u‖ ≤ 1) (qhat : κ → ℚ)
    (hq : ‖WithLp.toLp 2 (fun j => (qhat j : ℝ)) - weightedLocalMode w u‖ ≤ 1) :
    ‖WithLp.toLp 2 (fun j => (qhat j : ℝ))‖ ≤ 2 := by
  have hm := (weightedLocalMode_norm_le w hw u).trans hu
  have ht := norm_le_norm_sub_add (WithLp.toLp 2 (fun j => (qhat j : ℝ))) (weightedLocalMode w u)
  linarith

end Maxwell.Composition
