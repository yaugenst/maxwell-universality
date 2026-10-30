import Maxwell.Continuum.ParameterMaster
import Maxwell.Continuum.BoxGlobalMajorant

/-! The successful rational tests pay for the literal exponential terms
in the PEC residual estimate. -/

namespace Maxwell.Continuum.Parameters
open MasterConstants
attribute [local irreducible] Cs exponent

theorem globalBudget_cast (J m N L d : ℕ) (K : ℚ) :
    (globalBudget exponent J m N L d K : ℝ) =
      BoxCutoff.globalMajorant N J m K (alpha L d) L := by
  unfold globalBudget BoxCutoff.globalMajorant BoxCutoff.residualEnvelope
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_one, Rat.cast_natCast,
    Rat.cast_inv, Rat.cast_ofNat]
  change ((2 : ℝ)^exponent)^32*(1+N)^2*(1+J+m)^2*(1+(K : ℝ))^4*
    (1+(alpha L d : ℝ)⁻¹)^2*(L : ℝ)^100 = _
  rw [show (2 : ℝ)^exponent = Cs by unfold Cs; rfl]
  ring

theorem inverseBudget_cast (m N : ℕ) (τ : ℚ) :
    (inverseBudget m N τ : ℝ) = 64*(m : ℝ)*(N : ℝ)/(τ : ℝ) := by
  unfold inverseBudget
  push_cast
  rfl

theorem errorBudget_cast (m N : ℕ) (ε τ : ℚ) :
    (errorBudget m N ε τ : ℝ) =
      (ε : ℝ)/((2 : ℝ)^27*(64*(m : ℝ)*(N : ℝ)/(τ : ℝ))) := by
  unfold errorBudget
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, inverseBudget_cast]

theorem stageLength_real_cube_root (k : ℕ) :
    (stageLength k : ℝ)^(1/3 : ℝ) = ((2^k : ℕ) : ℝ) := by
  rw [← stageLength_cube_root, Nat.cast_pow]
  simpa only [one_div, Nat.cast_ofNat] using Real.pow_rpow_inv_natCast
    (Nat.cast_nonneg (2^k) : (0 : ℝ) ≤ (2^k : ℕ)) (by decide : (3 : ℕ) ≠ 0)

theorem selected_exponential_budgets (I : Input) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    let k := selectedOuterExponent I exponent (minimumLengthExponent exponent) ℓ hℓ
    let L := stageLength k
    let d := stageSpacing I exponent k
    let t := stageBuffer I exponent k
    let N := boxCount (stageSpan I exponent k) L t
    let Ξ := BoxCutoff.globalMajorant N I.J I.m I.K (alpha L d) L
    let e₀ := (errorBudget I.m N I.epsilon (stageTau I exponent k) : ℝ)
    Ξ*Real.exp (-cs*(L : ℝ)^(1/3 : ℝ)) ≤ e₀/4 ∧
    Ξ*Real.exp (-cs*((L : ℝ)*(t : ℝ))/(L : ℝ)) ≤ e₀/4 ∧
    (I.J : ℝ)*Cs*(L : ℝ)^5*Real.exp (-cs*(L : ℝ)) ≤ (zeta d : ℝ)^2/4 := by
  let k := selectedOuterExponent I exponent (minimumLengthExponent exponent) ℓ hℓ
  have ht := selected_master_tests I ℓ hℓ
  have hleak := rational_test_implies_master_exponential
    (globalBudget_nonneg exponent I.J I.m _ _ _ I.K) (2^k) ht.2.2.1
  have hbuffer := rational_test_implies_master_exponential
    (globalBudget_nonneg exponent I.J I.m _ _ _ I.K) (stageBuffer I exponent k) ht.2.1
  have htail := rational_test_implies_master_exponential
    (show (0 : ℚ) ≤ (I.J : ℚ)*2^exponent*(stageLength k : ℚ)^5 by positivity)
    (stageLength k) ht.2.2.2
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_mul, Rat.cast_natCast,
    globalBudget_cast] at hleak hbuffer htail
  rw [show (2 : ℝ)^exponent = Cs by unfold Cs; rfl] at htail
  have hL : (stageLength k : ℝ) ≠ 0 := by exact_mod_cast (stageLength_pos k).ne'
  dsimp only [k] at hL
  refine ⟨?_, ?_, ?_⟩
  · simpa only [stageLength_real_cube_root] using hleak
  · convert hbuffer using 1
    congr 2
    field_simp [hL]
    ring
  · exact htail

#print axioms selected_exponential_budgets

end Maxwell.Continuum.Parameters
