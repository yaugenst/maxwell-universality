import Maxwell.Continuum.CalibrationFiniteIteration

/-! Correctness of the executable finite Fourier mode, including both
rational square-root normalizations. The output approximates the literal
normalized real continuum mode without numerical-oracle assumptions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
namespace Maxwell.Continuum.Calibration.FiniteAlgorithm

open FreeFiber Supercell EffectiveMass NormedSpace MasterConstants

attribute [local irreducible] mode rawMode size precision workPrecision iterations realMode

private theorem final_precision_guard (p n extra ell k : ℕ) :
    p+(49+38*n)+4 ≤ powerWorkBits p n extra+2*ell+4*k+256 := by
  unfold powerWorkBits
  omega

private theorem final_small_guard (p n extra ell k : ℕ) :
    (49+38*n)+3 ≤ powerWorkBits p n extra+2*ell+4*k+256 := by
  unfold powerWorkBits
  omega

theorem mode_normalize_small (L r N : ℕ) :
    (1/2 : ℝ)^precision L r N ≤ (1/2 : ℝ)^(49+38*iterations N)/8 := by
  apply dyadic_normalize_small
  simpa only [precision,workPrecision,powerWorkPrecision,iterations] using
    final_small_guard (targetPrecision N) (iterations N) (Nat.clog 2 (iterations N+1))
      (lengthBits L) (rootBits L r N)

theorem mode_normalize_budget (L r N : ℕ) :
    10*(1/2 : ℝ)^precision L r N/(1/2 : ℝ)^(49+38*iterations N) ≤
      (1/2 : ℝ)^targetPrecision N := by
  apply dyadic_normalize_error
  simpa only [precision,workPrecision,powerWorkPrecision,iterations] using
    final_precision_guard (targetPrecision N) (iterations N) (Nat.clog 2 (iterations N+1))
      (lengthBits L) (rootBits L r N)

theorem mode_eq (L r N : ℕ) (z : ℚ) : mode L r N z =
    FourierData.normalizeData (precision L r N) (rawMode L r N z) := by
  unfold mode
  rfl

private theorem normalized_output_error (M : ℕ) [NeZero M]
    (v w : FourierData) (P : ℕ) (u : FieldL2) {δ ε : ℝ}
    (hδ : 0<δ) (hl : δ≤‖w.value‖) (hsmall : (1/2 : ℝ)^P≤δ/8)
    (hbudget : 10*(1/2 : ℝ)^P/δ≤ε)
    (hv : v=FourierData.normalizeData P w)
    (he : ‖normalize (embedding M w.value)-u‖≤ε) :
    ‖embedding M v.value-u‖≤2*ε := by
  have hn := normalizeData_physical_error M P w (by linarith)
  have hn' : ‖embedding M (FourierData.normalizeData P w).value-
      normalize (embedding M w.value)‖≤ε := by
    apply hn.trans
    apply le_trans _ hbudget
    apply div_le_div₀ (by positivity) (by nlinarith [pow_nonneg (by norm_num : (0 : ℝ)≤1/2) P]) hδ hl
  rw [hv]
  exact (norm_sub_le_norm_sub_add_norm_sub _ (normalize (embedding M w.value)) _).trans
    ((add_le_add hn' he).trans_eq (by ring))

private theorem target_double_bound (N : ℕ) :
    2*(1/2 : ℝ)^targetPrecision N≤(1/2 : ℝ)^N := by
  rw [targetPrecision,pow_add]
  norm_num
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ)≤1/2) N]

theorem mode_physical_error {L : ℕ} (hL : Ls≤(L : ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    ‖embedding (size L r N) (mode L r N z).value-
      realMode D (inverse_length_le_1024 hL)‖≤(1/2 : ℝ)^N :=
  (normalized_output_error (size L r N) (mode L r N z) (rawMode L r N z)
    (precision L r N) (realMode D (inverse_length_le_1024 hL))
    (by positivity) (rawMode_norm_lower hL r N z D) (mode_normalize_small L r N)
    (mode_normalize_budget L r N) (mode_eq L r N z)
    (rawMode_normalized_error hL r N z D)).trans (target_double_bound N)

theorem mode_norm_le {L : ℕ} (hL : Ls≤(L : ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) : ‖(mode L r N z).value‖≤2 := by
  have he := mode_physical_error hL r N z D
  have ht := norm_le_norm_sub_add (embedding (size L r N) (mode L r N z).value)
    (realMode D (inverse_length_le_1024 hL))
  rw [embedding_norm,realMode_norm] at ht
  have hh : (1/2 : ℝ)^N≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

#print axioms mode_physical_error
#print axioms mode_norm_le
end Maxwell.Continuum.Calibration.FiniteAlgorithm
