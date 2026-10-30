import Maxwell.Continuum.ContinuumRealizationPrecision
import Maxwell.Continuum.FiniteAuxiliaryMessageBits

/-! Fixed source-promise constants bound the actual inverse, residual
tolerance, and finite inputs on the same binary input scale. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.RealizationParameters

open MasterConstants Maxwell.Composition
attribute [local irreducible] Cs exponent Ls Parameters.sourceInput

def analysisBits (p : Source.Parameters) : ℕ := Parameters.sourceConditionExponent p
def inputBits (p : Source.Parameters) : ℕ := Parameters.sourceBudgetExponent p
abbrev logSize (S : Source.SparseSystem) : ℕ := Parameters.inputLog S.nnz
def scaleBits (p : Source.Parameters) (S : Source.SparseSystem) : ℕ := analysisBits p*logSize S

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)

theorem inverse_polynomial (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    702*(inverseBound p S hm : ℝ) ≤ (S.nnz : ℝ)^(analysisBits p) := by
  rw [inverseBound_eq]
  exact Parameters.source_condition_polynomial p S hm hm2 hu

theorem residual_polynomial (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    ((S.nnz : ℝ)^(2*Parameters.sourcePolynomialExponent p))⁻¹ ≤ (residual p S hm : ℝ) :=
  Parameters.source_residual_polynomial p S hm hm2 hu

theorem inverse_binary_real (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    (inverseBound p S hm : ℝ) ≤ (2 : ℝ)^(scaleBits p S) := by
  have hG : (inverseBound p S hm : ℝ) ≤ 702*(inverseBound p S hm : ℝ) := by
    nlinarith only [(inverseBound_pos p S hm).le]
  have hmR : (S.nnz : ℝ) ≤ (2 : ℝ)^(logSize S) := by exact_mod_cast Parameters.input_le_binary S.nnz
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg S.nnz) hmR (analysisBits p)
  rw [← pow_mul, Nat.mul_comm] at hp
  exact (hG.trans (inverse_polynomial p S hm hm2 hu)).trans hp

theorem inverse_binary (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    inverseBound p S hm ≤ (2 : ℚ)^(scaleBits p S) := by
  exact_mod_cast inverse_binary_real p S hm hm2 hu

theorem residual_binary_real (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    (1/2 : ℝ)^(scaleBits p S) ≤ (residual p S hm : ℝ) := by
  have hmR : (S.nnz : ℝ) ≤ (2 : ℝ)^(logSize S) := by exact_mod_cast Parameters.input_le_binary S.nnz
  have he : 2*Parameters.sourcePolynomialExponent p ≤ analysisBits p := by
    unfold analysisBits Parameters.sourceConditionExponent
    omega
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg S.nnz) hmR (2*Parameters.sourcePolynomialExponent p)
  rw [← pow_mul] at hp
  have hh := hp.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (show logSize S*(2*Parameters.sourcePolynomialExponent p) ≤ scaleBits p S by
      simpa only [scaleBits, Nat.mul_comm] using Nat.mul_le_mul_right (logSize S) he))
  have hmpos : (0 : ℝ) < S.nnz := by exact_mod_cast hm
  have hi := (inv_le_inv₀ (show (0 : ℝ) < 2^(scaleBits p S) by positivity)
    (show (0 : ℝ) < (S.nnz : ℝ)^(2*Parameters.sourcePolynomialExponent p) by positivity)).mpr hh
  apply le_trans _ (residual_polynomial p S hm hm2 hu)
  simpa only [one_div, inv_pow] using hi

theorem residual_binary (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    (1/2 : ℚ)^(scaleBits p S) ≤ residual p S hm := by
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    residual_binary_real p S hm hm2 hu

theorem input_binary (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    budget p S hm ≤ (2 : ℚ)^(inputBits p*logSize S) ∧
    (sites p S hm : ℚ) ≤ (2 : ℚ)^(inputBits p*logSize S) ∧
    (epsilon p S hm)⁻¹ ≤ (2 : ℚ)^(inputBits p*logSize S) := by
  have h := Parameters.sourceInput_binary p S hm hm2 hu
  have hJ := h.J
  rw [input_sites] at hJ
  exact ⟨h.K, hJ, h.epsilon⟩

theorem energyPrecision_linear (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    energyPrecision p S hm ≤ (180*Parameters.sourceMagnitude p+60)*logSize S := by
  have h := (Parameters.source_bits p S hm hm2 hu).1
  have hℓ := Parameters.inputLog_pos S.nnz
  change (length p S hm).bits.length ≤ 45*Parameters.sourceMagnitude p+6*logSize S+7 at h
  unfold energyPrecision
  nlinarith only [h, hℓ]

theorem messageRangeBits_linear (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    FiniteAuxiliary.messageRangeBits (inverseBound p S hm) S.nnz ≤
      (analysisBits p+4)*logSize S := by
  have h := FiniteAuxiliary.messageRangeBits_le (inverse_binary p S hm hm2 hu)
    (Parameters.input_le_binary S.nnz)
  have hℓ := Parameters.inputLog_pos S.nnz
  change _ ≤ scaleBits p S+logSize S+3 at h
  unfold scaleBits at h
  nlinarith only [h, hℓ]

#print axioms inverse_binary
#print axioms residual_binary
#print axioms messageRangeBits_linear

end Maxwell.Continuum.RealizationParameters
