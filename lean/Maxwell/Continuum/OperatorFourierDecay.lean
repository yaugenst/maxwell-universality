import Maxwell.Continuum.WellFourierDecay

/-! Dimension-free Fourier decay for actual Banach-valued symbols. This
applies to the full fiber operator, not merely to finitely many entries. -/

noncomputable section

namespace Maxwell.Continuum.OperatorFourier

open MeasureTheory Set Metric
open scoped FourierTransform

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

def directionalDerivative (K : ℕ) (f : Space → F) (y v : Space) : F :=
  iteratedFDeriv ℝ K f y (fun _ => v)

def angularFourier (f : Space → F) (p : Space) : F :=
  𝓕 f ((2 * Real.pi)⁻¹ • p)

theorem iteratedFDeriv_integrable (f : Space → F)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (K : ℕ) :
    Integrable (iteratedFDeriv ℝ K f) (volume : Measure Space) :=
  (hf.continuous_iteratedFDeriv (by simp)).integrable_of_hasCompactSupport
    (hfc.iteratedFDeriv K)

theorem fourier_directional_norm (f : Space → F)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (K : ℕ) (ξ v : Space) :
    ‖𝓕 (fun y => directionalDerivative K f y v) ξ‖ =
      (2 * Real.pi * |inner ℝ ξ v|) ^ K * ‖𝓕 f ξ‖ := by
  have hint := iteratedFDeriv_integrable f hf hfc
  have h := congrArg (fun A => A ξ (fun _ : Fin K => v))
    (Real.fourier_iteratedFDeriv hf (fun n _ => hint n) (n := K) (by simp))
  rw [Real.fourier_continuousMultilinearMap_apply (hint K)] at h
  change 𝓕 (fun y => directionalDerivative K f y v) ξ = _ at h
  rw [h]
  simp only [VectorFourier.fourierPowSMulRight_apply, neg_apply,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_smul, norm_pow, norm_neg,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  change (‖(2 : ℂ)‖ * Real.pi) ^ K *
    (|inner ℝ ξ v| ^ K * ‖𝓕 f ξ‖) = _
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  ring

theorem fourier_directional_le (f : Space → F)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (K : ℕ) (ξ v : Space) :
    (2 * Real.pi * |inner ℝ ξ v|) ^ K * ‖𝓕 f ξ‖ ≤
      ∫ y, ‖directionalDerivative K f y v‖ := by
  rw [← fourier_directional_norm f hf hfc K ξ v]
  have h := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar
    (volume : Measure Space) (innerₗ Space) (fun y => directionalDerivative K f y v) ξ
  simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, innerₗ_apply_apply] using h

theorem integral_directional_le (f : Space → F)
    (hs : tsupport f ⊆ closedBall (0 : Space) 1)
    (K : ℕ) (v : Space) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ y, ‖directionalDerivative K f y v‖ ≤ C) :
    (∫ y, ‖directionalDerivative K f y v‖) ≤ 8 * C := by
  have hi : Integrable ((closedBall (0 : Space) 1).indicator (fun _ : Space => C)) volume :=
    (integrableOn_const (isCompact_closedBall (0 : Space) 1).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  have hbound : ∀ y, ‖directionalDerivative K f y v‖ ≤
      (closedBall (0 : Space) 1).indicator (fun _ : Space => C) y := by
    intro y
    by_cases hy : y ∈ closedBall (0 : Space) 1
    · rw [indicator_of_mem hy]
      exact hb y
    · rw [indicator_of_notMem hy]
      have hz : iteratedFDeriv ℝ K f y = 0 := by
        apply Function.notMem_support.mp
        intro hm
        exact hy (hs (support_iteratedFDeriv_subset K hm))
      simp only [directionalDerivative, hz, zero_apply, norm_zero, le_refl]
  calc
    (∫ y, ‖directionalDerivative K f y v‖) ≤
        ∫ y, (closedBall (0 : Space) 1).indicator (fun _ : Space => C) y :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hi
        (Filter.Eventually.of_forall hbound)
    _ = (volume : Measure Space).real (closedBall 0 1) * C := by
      rw [integral_indicator_const C measurableSet_closedBall, smul_eq_mul]
    _ ≤ 8 * C := mul_le_mul_of_nonneg_right Well.unitBall_volume_le_eight hC

theorem angularFourier_gevrey_bound (f : Space → F)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hs : tsupport f ⊆ closedBall (0 : Space) 1)
    {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hb : ∀ (K : ℕ) (y v : Space), ‖v‖ ≤ 1 →
      ‖directionalDerivative K f y v‖ ≤ C * A ^ K * (K.factorial : ℝ) ^ 2)
    (p : Space) (K : ℕ) :
    ‖p‖ ^ K * ‖angularFourier f p‖ ≤ 8 * C * A ^ K * (K.factorial : ℝ) ^ 2 := by
  by_cases hp : p = 0
  · subst p
    cases K with
    | zero =>
      have h := fourier_directional_le f hf hfc 0 0 0
      have hh := integral_directional_le f hs 0 0 C hC
        (fun y => by simpa using hb 0 y 0 (by simp))
      simpa [angularFourier] using h.trans hh
    | succ K => simp; positivity
  · have hn : 0 < ‖p‖ := norm_pos_iff.mpr hp
    let v : Space := ‖p‖⁻¹ • p
    let ξ : Space := (2 * Real.pi)⁻¹ • p
    have hv : ‖v‖ ≤ 1 := by
      dsimp [v]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hip : 2 * Real.pi * |inner ℝ ξ v| = ‖p‖ := by
      dsimp [ξ, v]
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      rw [abs_of_nonneg (by positivity)]
      field_simp
    have h := fourier_directional_le f hf hfc K ξ v
    rw [hip] at h
    have hh := integral_directional_le f hs K v
      (C * A ^ K * (K.factorial : ℝ) ^ 2) (by positivity) (fun y => hb K y v hv)
    simpa only [angularFourier, mul_assoc] using h.trans hh

theorem gevrey_decay_scaled {r V C A : ℝ} (hr : 0 ≤ r) (hC : 0 < C) (hA : 0 < A)
    (hb : ∀ K : ℕ, r ^ K * V ≤ 8 * C * A ^ K * (K.factorial : ℝ) ^ 2) :
    V ≤ 24 * C * Real.exp (-Real.sqrt (400 * r / A) / 64) := by
  by_cases hr0 : r = 0
  · have h := hb 0
    simp only [hr0, mul_zero, zero_div, Real.sqrt_zero, neg_zero, Real.exp_zero,
      Nat.factorial_zero, Nat.cast_one, one_pow, mul_one] at h ⊢
    linarith
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have ht : ∀ K : ℕ, (400 * r / A) ^ K * (V / C) ≤
      8 * (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by
    intro K
    have hmul := mul_le_mul_of_nonneg_left (hb K)
      (show 0 ≤ (400 / A : ℝ)^K / C by positivity)
    calc
      (400 * r / A) ^ K * (V / C) =
          ((400 / A : ℝ)^K / C) * (r^K * V) := by
        rw [show 400 * r / A = (400 / A) * r by ring, mul_pow]
        ring
      _ ≤ ((400 / A : ℝ)^K / C) * (8 * C * A^K * (K.factorial : ℝ)^2) := hmul
      _ = 8 * (400 : ℝ)^K * (K.factorial : ℝ)^2 := by
        rw [div_pow]
        field_simp
  have h := Well.gevrey_decay_optimization (400 * r / A) (V / C) (by positivity) ht
  have h' := (div_le_iff₀ hC).mp h
  nlinarith

theorem angularFourier_gevrey_decay (f : Space → F)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hs : tsupport f ⊆ closedBall (0 : Space) 1)
    {C A : ℝ} (hC : 0 < C) (hA : 0 < A)
    (hb : ∀ (K : ℕ) (y v : Space), ‖v‖ ≤ 1 →
      ‖directionalDerivative K f y v‖ ≤ C * A ^ K * (K.factorial : ℝ) ^ 2)
    (p : Space) :
    ‖angularFourier f p‖ ≤ 24 * C * Real.exp (-Real.sqrt (400 * ‖p‖ / A) / 64) :=
  gevrey_decay_scaled (norm_nonneg p) hC hA
    (angularFourier_gevrey_bound f hf hfc hs hC.le hA.le hb p)

#print axioms angularFourier_gevrey_decay

end Maxwell.Continuum.OperatorFourier
