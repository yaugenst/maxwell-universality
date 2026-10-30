import Maxwell.Continuum.ParameterResources
import Maxwell.Continuum.ParameterConstants
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Literal master-constant specialization of the terminating rational
encoder, with the real-log input scale identified exactly. -/

namespace Maxwell.Continuum.Parameters
open MasterConstants
attribute [local irreducible] exponent Cs

 def minimumLengthExponent (e : ℕ) : ℕ := (64*e+2)/3

 theorem ceil_third (n : ℕ) : ⌈(n : ℝ)/3⌉₊ = (n+2)/3 := by
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
    have h : n ≤ ((n+2)/3)*3 := by omega
    exact_mod_cast h
  · have h := Nat.le_ceil ((n : ℝ)/3)
    have hr := (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mp h
    have hn : n ≤ ⌈(n : ℝ)/3⌉₊*3 := by exact_mod_cast hr
    omega

 theorem minimumLengthExponent_eq : minimumLengthExponent exponent = lengthExponent := by
  symm
  simpa only [lengthExponent, minimumLengthExponent, Nat.cast_mul, Nat.cast_ofNat] using ceil_third (64*exponent)

 theorem inputLog_real (m : ℕ) :
    inputLog m = 1+⌈Real.log (2+(m : ℝ))/Real.log 2⌉₊ := by
  rw [inputLog, ← Real.natCeil_logb_natCast 2 (m+2)]
  simp only [Real.logb, Nat.cast_add, Nat.cast_ofNat, add_comm]

 theorem selectedLength_master_lower (I : Input) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    Ls ≤ (stageLength (selectedOuterExponent I exponent (minimumLengthExponent exponent) ℓ hℓ) : ℝ) := by
  have hk := selectedOuter_ge_base I exponent (minimumLengthExponent exponent) ℓ hℓ
  rw [minimumLengthExponent_eq] at hk
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 8) hk
  simpa only [Ls, stageLength, Nat.cast_pow, Nat.cast_ofNat, minimumLengthExponent_eq] using hpow

 theorem stageLength_cube_root (k : ℕ) : (2^k : ℕ)^3 = stageLength k := by
  unfold stageLength
  rw [show (8 : ℕ) = 2^3 by decide, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- All five spacing tests, both final rational tests, and the buffer test
hold at the actual returned power of eight. -/
 theorem selected_master_tests (I : Input) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    let k := selectedOuterExponent I exponent (minimumLengthExponent exponent) ℓ hℓ
    SpacingTest exponent (stageLength k) I.K I.epsilon (stageSpacing I exponent k) ∧
    BufferTest exponent I.J I.m (stageLength k) (stageSpacing I exponent k) (stageSpan I exponent k)
      I.K I.epsilon (stageTau I exponent k) (stageBuffer I exponent k) ∧
    LeakageTest I exponent k ∧ TailTest I exponent k := by
  refine ⟨selectedSpacing_spec _ _ _ _ _ _, stageBuffer_spec _ _ _, ?_⟩
  exact selectedOuter_spec _ _ _ _ _

#print axioms selectedLength_master_lower
#print axioms selected_master_tests

end Maxwell.Continuum.Parameters
