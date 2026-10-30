import Maxwell.Continuum.ParameterGeometry
import Maxwell.Continuum.ParameterSourcePrecision
import Maxwell.Continuum.PECBoxDetuning

/-! The selected rational budgets applied to the actual PEC box spectrum.
The condition bound and residual tolerance are polynomial in the original
number of nonzeros, and the random seed is logarithmic. -/

noncomputable section
namespace Maxwell.Continuum.Parameters
open MasterConstants
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
attribute [local irreducible] exponent Cs

def sourcePhysicalLengths (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    ModeCount.BoxLengths := fun j => 2*sourceBox p S hm (sourceStage p S hm) j

def sourceSpectralBudget (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) : ℕ :=
  ModeCount.spectralCountBudget (sourcePhysicalLengths p S hm)

theorem sourcePhysicalLengths_pos (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (j : Fin 3) : 0 < sourcePhysicalLengths p S hm j := by
  unfold sourcePhysicalLengths sourceBox
  omega

theorem sourceSpectralBudget_eq (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    sourceSpectralBudget p S hm =
      boxCount (stageSpan (sourceInput p S hm) exponent (sourceStage p S hm))
        (stageLength (sourceStage p S hm))
        (stageBuffer (sourceInput p S hm) exponent (sourceStage p S hm)) := rfl

theorem sourceSpectralBudget_pos (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    0 < sourceSpectralBudget p S hm := by rw [sourceSpectralBudget_eq]; exact boxCount_pos _ _ _

def sourceDetuningRadius (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) : ℚ :=
  stageTau (sourceInput p S hm) exponent (sourceStage p S hm)

def sourceResidualTolerance (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) : ℚ :=
  errorBudget S.nnz (sourceSpectralBudget p S hm) (sourceInput p S hm).epsilon
    (sourceDetuningRadius p S hm)

theorem sourceDetuningRadius_pos (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    0 < sourceDetuningRadius p S hm := stageTau_pos _ _ _

theorem sourceResidualTolerance_pos (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    0 < sourceResidualTolerance p S hm :=
  errorBudget_pos hm (sourceSpectralBudget_pos p S hm) (sourceInput p S hm).epsilon_pos
    (sourceDetuningRadius_pos p S hm)

theorem sourceDetuningRadius_upper (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    sourceDetuningRadius p S hm ≤ 1/64 := by
  let I := sourceInput p S hm
  let k := sourceStage p S hm
  have h := (tau_bracket (stageLength k) (stageSpacing I exponent k) (stageLength_pos k)).2
  have hL : (1 : ℚ) ≤ stageLength k := by exact_mod_cast stageLength_pos k
  have hz := pow_le_one₀ (zeta_pos (stageSpacing I exponent k)).le
    (zeta_le_one (stageSpacing I exponent k)) (n := 2)
  have hL4 : 1 ≤ (stageLength k : ℚ)^4 := one_le_pow₀ hL
  apply h.trans
  unfold tauBudget
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2^24*(stageLength k : ℚ)^4)).mpr
  nlinarith only [hz,hL4]

private theorem shifted_size_power {m a : ℕ} (hm : 2 ≤ m) :
    (m+2 : ℚ)^a ≤ (m : ℚ)^(2*a) := by
  have hmq : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hbase : (m+2 : ℚ) ≤ (m : ℚ)^2 := by nlinarith
  simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ m+2) hbase a

def sourceConditionExponent (p : Source.Parameters) : ℕ := 2*sourcePolynomialExponent p+10

theorem source_condition_polynomial (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    702*Detuning.inverseBudget S.nnz (sourceSpectralBudget p S hm) (sourceDetuningRadius p S hm) ≤
      (S.nnz : ℝ)^sourceConditionExponent p := by
  have hb := (source_inverse_scales p S hm hm2 hunit).2.2.1
  change inverseBudget S.nnz _ _ ≤ _ at hb
  rw [← sourceSpectralBudget_eq] at hb
  have hp := hb.trans (shifted_size_power hm2)
  have hmQ : (2 : ℚ) ≤ S.nnz := by exact_mod_cast hm2
  have hc : (702 : ℚ) ≤ (S.nnz : ℚ)^10 :=
    (by norm_num : (702 : ℚ) ≤ 2^10).trans (pow_le_pow_left₀ (by norm_num) hmQ 10)
  have hprod := mul_le_mul hc hp
    (inverseBudget_pos hm (sourceSpectralBudget_pos p S hm) (sourceDetuningRadius_pos p S hm)).le
    (by positivity : (0 : ℚ) ≤ (S.nnz : ℚ)^10)
  have hq : 702*inverseBudget S.nnz (sourceSpectralBudget p S hm) (sourceDetuningRadius p S hm) ≤
      (S.nnz : ℚ)^sourceConditionExponent p := by
    apply hprod.trans_eq
    rw [← pow_add]
    congr 1
    unfold sourceConditionExponent
    omega
  have hr : ((702*inverseBudget S.nnz (sourceSpectralBudget p S hm) (sourceDetuningRadius p S hm) : ℚ) : ℝ) ≤
      (((S.nnz : ℚ)^sourceConditionExponent p : ℚ) : ℝ) := Rat.cast_le.mpr hq
  simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast,inverseBudget_cast,
    Detuning.inverseBudget] using hr

theorem source_residual_polynomial (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    ((S.nnz : ℝ)^(2*sourcePolynomialExponent p))⁻¹ ≤ (sourceResidualTolerance p S hm : ℝ) := by
  have hb := (source_inverse_scales p S hm hm2 hunit).2.2.2.1
  change (errorBudget S.nnz _ _ _)⁻¹ ≤ _ at hb
  rw [← sourceSpectralBudget_eq] at hb
  have hp := hb.trans (shifted_size_power hm2)
  have h := (inv_le_inv₀ (by positivity : (0 : ℚ) < (S.nnz : ℚ)^(2*sourcePolynomialExponent p))
    (inv_pos.mpr (sourceResidualTolerance_pos p S hm))).mpr hp
  rw [inv_inv] at h
  have hr : ((((S.nnz : ℚ)^(2*sourcePolynomialExponent p))⁻¹ : ℚ) : ℝ) ≤
      (sourceResidualTolerance p S hm : ℝ) := Rat.cast_le.mpr h
  simpa only [Rat.cast_inv,Rat.cast_pow,Rat.cast_natCast] using hr

theorem source_residual_precision_bits (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    Realization.precisionBits (sourceResidualTolerance p S hm) (sourceResidualTolerance_pos p S hm) ≤
      2^(12*sourceMagnitude p)*inputLog S.nnz := by
  have hI := sourceInput_binary p S hm hm2 hunit
  have hM := sourceMagnitude_bounds p
  have hE := selected_budget_exponent hI hM.1 hM.2.1 hM.2.2.1 hM.2.2.2 (inputLog_pos S.nnz)
  change stageBudgetExponent exponent (sourceBudgetExponent p) (inputLog S.nnz) (sourceStage p S hm)
    (stageSpacing (sourceInput p S hm) exponent (sourceStage p S hm))
    (stageBuffer (sourceInput p S hm) exponent (sourceStage p S hm)) ≤ _ at hE
  have hb := (stage_numeric_budgets hI exponent (sourceStage p S hm)
    (stageBuffer (sourceInput p S hm) exponent (sourceStage p S hm))).2.2.2.1
  change (errorBudget S.nnz _ _ _)⁻¹ ≤ _ at hb
  rw [← sourceSpectralBudget_eq] at hb
  have hp := hb.trans (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hE)
  apply precisionBits_le_of_binary (sourceResidualTolerance_pos p S hm)
  have hh := (inv_le_inv₀ (by positivity : (0 : ℚ) < 2^(2^(12*sourceMagnitude p)*inputLog S.nnz))
    (inv_pos.mpr (sourceResidualTolerance_pos p S hm))).mpr hp
  simpa only [inv_inv,← inv_pow,one_div] using hh

theorem source_random_bits (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    Detuning.randomBits S.nnz (sourceSpectralBudget p S hm) ≤
      (7+2^(12*sourceMagnitude p))*inputLog S.nnz := by
  have hI := sourceInput_binary p S hm hm2 hunit
  have hM := sourceMagnitude_bounds p
  have hE := selected_budget_exponent hI hM.1 hM.2.1 hM.2.2.1 hM.2.2.2 (inputLog_pos S.nnz)
  change stageBudgetExponent exponent (sourceBudgetExponent p) (inputLog S.nnz) (sourceStage p S hm)
    (stageSpacing (sourceInput p S hm) exponent (sourceStage p S hm))
    (stageBuffer (sourceInput p S hm) exponent (sourceStage p S hm)) ≤ _ at hE
  have hN := stageCount_binary hI exponent (sourceStage p S hm)
    (stageBuffer (sourceInput p S hm) exponent (sourceStage p S hm))
  rw [← sourceSpectralBudget_eq] at hN
  have hNE : (sourceSpectralBudget p S hm : ℚ) ≤ (2 : ℚ)^(2^(12*sourceMagnitude p)*inputLog S.nnz) := by
    apply hN.trans
    apply pow_le_pow_right₀ (by norm_num)
    apply le_trans _ hE
    unfold stageCountExponent stageBudgetExponent
    simp only [Nat.mul_assoc]
    omega
  have hclog := Nat.clog_le_of_le_pow (show sourceSpectralBudget p S hm ≤
    2^(2^(12*sourceMagnitude p)*inputLog S.nnz) by exact_mod_cast hNE)
  have hmclog := Nat.clog_le_of_le_pow (input_le_binary S.nnz)
  have hh := Detuning.randomBits_le S.nnz (sourceSpectralBudget p S hm)
  have hℓ := inputLog_pos S.nnz
  rw [Nat.add_mul]
  omega

#print axioms sourceSpectralBudget_eq
#print axioms source_condition_polynomial
#print axioms source_residual_polynomial
#print axioms source_residual_precision_bits
#print axioms source_random_bits

end Maxwell.Continuum.Parameters
