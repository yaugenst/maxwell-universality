import Maxwell.Continuum.ParameterPhysicalBudgets
import Maxwell.Continuum.ParameterTuning

/-! The actual source-selected parameters discharge the scalar hypotheses
of continuum assembly. No successful-search or asymptotic premise remains. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.RealizationParameters

open MasterConstants Maxwell.Composition
attribute [local irreducible] Cs exponent Ls lengthExponent Parameters.sourceInput

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)

abbrev precision : ℕ := (SelectedInput.input p S hm).precision
abbrev kappa : ℚ := (SelectedInput.input p S hm).sourceBound
abbrev accuracy : ℚ := (SelectedInput.input p S hm).accuracy
abbrev budget : ℚ := (Parameters.sourceInput p S hm).K
abbrev epsilon : ℚ := (Parameters.sourceInput p S hm).epsilon
abbrev stage : ℕ := Parameters.sourceStage p S hm
abbrev length : ℕ := Parameters.stageLength (stage p S hm)
abbrev spacing : ℕ := Parameters.stageSpacing (Parameters.sourceInput p S hm) exponent (stage p S hm)
abbrev bufferSteps : ℕ := Parameters.stageBuffer (Parameters.sourceInput p S hm) exponent (stage p S hm)
abbrev buffer : ℕ := length p S hm * bufferSteps p S hm
abbrev zeta : ℚ := Parameters.zeta (spacing p S hm)
abbrev alpha : ℚ := Parameters.alpha (length p S hm) (spacing p S hm)
abbrev radius : ℚ := Parameters.sourceDetuningRadius p S hm
abbrev count : ℕ := Parameters.sourceSpectralBudget p S hm
abbrev residual : ℚ := Parameters.sourceResidualTolerance p S hm
abbrev inverseBound : ℚ := Parameters.inverseBudget S.nnz (count p S hm) (radius p S hm)

theorem length_master : Ls ≤ (length p S hm : ℝ) := Parameters.source_master_length p S hm

theorem length_pos : 0 < length p S hm := Parameters.stageLength_pos _

theorem length_even : Even (length p S hm) := by
  have hk : stage p S hm ≠ 0 := by
    intro he
    have hl := length_master p S hm
    change Ls ≤ (Parameters.stageLength (stage p S hm) : ℝ) at hl
    rw [he] at hl
    norm_num only [Parameters.stageLength, pow_zero, Nat.cast_one] at hl
    have ht := power_lt_Ls (n := 0) (by have := exponent_large; omega)
    norm_num only [pow_zero] at ht
    exact (not_lt_of_ge hl) ht
  exact Even.pow_of_ne_zero (by decide : Even (8 : ℕ)) hk

theorem spacing_pos : 1 ≤ spacing p S hm := Parameters.selectedSpacing_pos _ _ _ _ _ _

theorem budget_ge_one : (1 : ℝ) ≤ budget p S hm := by
  change (1 : ℝ) ≤ (Parameters.sourceInput p S hm).K
  rw [Parameters.sourceInput]
  exact_mod_cast SelectedInstance.Input.logicalBudget_ge_one (SelectedInput.input p S hm)

theorem kappa_ge_one : (1 : ℝ) ≤ kappa p S hm := by
  exact_mod_cast (SelectedInput.input p S hm).sourceBound_ge_one

theorem epsilon_pos : (0 : ℝ) < epsilon p S hm := by
  exact_mod_cast (Parameters.sourceInput p S hm).epsilon_pos

theorem epsilon_le_one : (epsilon p S hm : ℝ) ≤ 1 := by
  have he := SelectedInstance.Input.epsilon_half (SelectedInput.input p S hm)
  have hq : epsilon p S hm ≤ 1 := by
    change (Parameters.sourceInput p S hm).epsilon ≤ 1
    rw [Parameters.sourceInput]
    linarith only [he]
  exact_mod_cast hq

theorem zeta_pos : 0 < zeta p S hm := Parameters.zeta_pos _

theorem zeta_le_one : zeta p S hm ≤ 1 := Parameters.zeta_le_one _

theorem zeta_cast : (zeta p S hm : ℝ) = ((3 : ℝ)^(spacing p S hm))⁻¹ := by
  change (((1/3 : ℚ)^spacing p S hm : ℚ) : ℝ) = _
  push_cast
  simp only [one_div, inv_pow]

theorem alpha_pos : (0 : ℝ) < alpha p S hm := by
  exact_mod_cast Parameters.alpha_pos (length_pos p S hm) (spacing p S hm)

theorem alpha_cast : (alpha p S hm : ℝ) =
    (cu/4)*(length p S hm : ℝ)^2*(8 : ℝ)^(-(spacing p S hm : ℝ)) := by
  simp only [alpha, Parameters.alpha, Rat.cast_mul, Rat.cast_inv, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), Real.rpow_natCast,
    one_div, inv_pow]
  have hc : ((2 : ℝ)^1026)⁻¹ = cu/4 := by
    rw [show (1026 : ℕ) = 1024+2 by omega, pow_add]
    rw [show (2 : ℝ)^2 = 4 by norm_num, mul_inv_rev, cu, div_eq_mul_inv, mul_comm]
  rw [hc]

theorem spacing_bounds :
    ds ≤ (spacing p S hm : ℝ) ∧
    Cs^4*(length p S hm : ℝ) ≤ (spacing p S hm : ℝ)^15 ∧
    (alpha p S hm : ℝ) ≤ 1 ∧
    Cs^4*(length p S hm : ℝ)^12*(zeta p S hm : ℝ) ≤ (epsilon p S hm : ℝ)/2^24 ∧
    Cs^4*(length p S hm : ℝ)^12*(zeta p S hm : ℝ)^2 ≤
      (alpha p S hm : ℝ)*(epsilon p S hm : ℝ)/(2^24*(budget p S hm : ℝ)) := by
  simpa only [Cs, ds] using Parameters.spacingTest_real (Parameters.source_tests p S hm).1

theorem zeta_square_le_alpha : (zeta p S hm : ℝ)^2 ≤ (alpha p S hm : ℝ) :=
  Parameters.second_test_square_le (length_master p S hm) (alpha_pos p S hm)
    (budget_ge_one p S hm) (epsilon_le_one p S hm) (spacing_bounds p S hm).2.2.2.2

theorem radius_pos : (0 : ℝ) < radius p S hm := by
  exact_mod_cast Parameters.sourceDetuningRadius_pos p S hm

theorem radius_upper : (radius p S hm : ℝ) ≤ 1/64 := by
  have h := Rat.cast_le (K := ℝ) |>.mpr (Parameters.sourceDetuningRadius_upper p S hm)
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  exact h

theorem radius_budget : (radius p S hm : ℝ) ≤
    (zeta p S hm : ℝ)^2/(2^24*(length p S hm : ℝ)^4) := by
  have ht := (Parameters.tau_bracket (length p S hm) (spacing p S hm) (length_pos p S hm)).2
  change radius p S hm ≤ Parameters.tauBudget (length p S hm) (spacing p S hm) at ht
  unfold Parameters.tauBudget at ht
  exact_mod_cast ht

theorem detuning_bounds {σ : ℝ} (hσ : σ ≤ (radius p S hm : ℝ)) :
    σ ≤ (length p S hm : ℝ)⁻¹^4/64 ∧
    16*σ*(length p S hm : ℝ)^4 ≤ (zeta p S hm : ℝ)^2/2^20 := by
  have hL : (0 : ℝ) < length p S hm := by exact_mod_cast length_pos p S hm
  have hz0 : (0 : ℝ) ≤ zeta p S hm := by exact_mod_cast (zeta_pos p S hm).le
  have hz1 : (zeta p S hm : ℝ) ≤ 1 := by exact_mod_cast zeta_le_one p S hm
  have hsq : (zeta p S hm : ℝ)^2 ≤ 1 := pow_le_one₀ hz0 hz1
  have ht := hσ.trans (radius_budget p S hm)
  have hmul := (le_div_iff₀ (show (0 : ℝ) < 2^24*(length p S hm : ℝ)^4 by positivity)).mp ht
  constructor
  · rw [inv_pow, inv_eq_one_div, div_div, mul_comm _ (64 : ℝ)]
    apply (le_div_iff₀ (show (0 : ℝ) < 64*(length p S hm : ℝ)^4 by positivity)).mpr
    nlinarith only [hmul, hsq]
  · nlinarith only [hmul]

theorem inverseBound_pos : (0 : ℝ) < inverseBound p S hm := by
  exact_mod_cast Parameters.inverseBudget_pos hm (Parameters.sourceSpectralBudget_pos p S hm)
    (Parameters.sourceDetuningRadius_pos p S hm)

theorem inverseBound_eq : (inverseBound p S hm : ℝ) =
    Detuning.inverseBudget S.nnz (count p S hm) (radius p S hm) :=
  Parameters.inverseBudget_cast _ _ _

theorem inverseBound_ge_one : (1 : ℝ) ≤ inverseBound p S hm := by
  rw [Parameters.inverseBudget_cast]
  have hm1 : (1 : ℝ) ≤ S.nnz := by exact_mod_cast hm
  have hN1 : (1 : ℝ) ≤ count p S hm := by
    exact_mod_cast Parameters.sourceSpectralBudget_pos p S hm
  apply (le_div_iff₀ (radius_pos p S hm)).mpr
  have hmn : 1 ≤ (S.nnz : ℝ)*(count p S hm : ℝ) :=
    one_le_mul_of_one_le_of_one_le hm1 hN1
  have hr := radius_upper p S hm
  nlinarith only [hmn, hr]

theorem residual_pos : (0 : ℝ) < residual p S hm := by
  exact_mod_cast Parameters.sourceResidualTolerance_pos p S hm

theorem residual_identity : (inverseBound p S hm : ℝ)*(residual p S hm : ℝ) =
    (epsilon p S hm : ℝ)/2^27 := by
  change (inverseBound p S hm : ℝ)*
    ((epsilon p S hm/(2^27*inverseBound p S hm) : ℚ) : ℝ) = _
  push_cast
  field_simp [(inverseBound_pos p S hm).ne']

theorem residual_half : (residual p S hm : ℝ) ≤ 1/2 := by
  have he := residual_identity p S hm
  have hle := le_mul_of_one_le_left (residual_pos p S hm).le (inverseBound_ge_one p S hm)
  rw [he] at hle
  exact hle.trans (by linarith only [epsilon_le_one p S hm])

#print axioms spacing_bounds
#print axioms detuning_bounds
#print axioms residual_identity

end Maxwell.Continuum.RealizationParameters
