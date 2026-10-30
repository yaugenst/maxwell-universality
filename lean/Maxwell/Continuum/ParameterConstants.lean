import Maxwell.Continuum.MasterConstants
import Maxwell.Continuum.ParameterCasts

/-! Proof-level specialization of the executable rational searches to the
literal master constants in the continuum construction. -/

namespace Maxwell.Continuum.Parameters

open MasterConstants
attribute [local irreducible] exponent lengthExponent

noncomputable def masterCs : ℚ := (2 : ℚ)^exponent
noncomputable def masterLength : ℕ := 8^lengthExponent

theorem masterCs_cast : (masterCs : ℝ) = Cs := by
  unfold masterCs
  rw [Rat.cast_pow]
  rfl

theorem mastercs_cast : (mastercs : ℝ) = cs := cast_inverse_power 1024

theorem masterLength_cast : (masterLength : ℝ) = Ls := by
  unfold masterLength
  rw [Nat.cast_pow]
  rfl

theorem masterCs_pos : 0 < masterCs := by unfold masterCs; positivity

theorem masterCs_ge_one : 1 ≤ masterCs := one_le_pow₀ (by norm_num)

theorem rational_test_implies_master_exponential {A B : ℚ} (hA : 0 ≤ A) (t : ℕ)
    (htest : A*rationalDecay t ≤ B) : (A : ℝ)*Real.exp (-cs*(t : ℝ)) ≤ B := by
  simpa only [mastercs_cast] using rational_test_implies_exponential hA t htest

/-- All five manuscript tests hold for the returned literal doubling search. -/
theorem selectedSpacing_master_spec (L : ℕ) (K ε : ℚ) (hK : 0 < K) (hε : 0 < ε) :
    let d := selectedSpacing exponent L K ε hK hε
    ds ≤ (d : ℝ) ∧ Cs^4*(L : ℝ) ≤ (d : ℝ)^15 ∧ (alpha L d : ℝ) ≤ 1 ∧
    Cs^4*(L : ℝ)^12*(zeta d : ℝ) ≤ (ε : ℝ)/2^24 ∧
    Cs^4*(L : ℝ)^12*(zeta d : ℝ)^2 ≤
      (alpha L d : ℝ)*(ε : ℝ)/(2^24*(K : ℝ)) :=
  spacingTest_real (selectedSpacing_spec exponent L K ε hK hε)

#print axioms selectedSpacing_master_spec

end Maxwell.Continuum.Parameters
