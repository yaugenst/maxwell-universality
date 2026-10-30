import Maxwell.Continuum.ParameterSpacingSearch

/-! Generic cast lemmas keep fixed astronomical integers symbolic when the
arithmetic encoder is specialized to the continuum master constants. -/

namespace Maxwell.Continuum.Parameters

theorem cast_spacing_power (e : ℕ) : (((2^e)^8 : ℕ) : ℝ) = ((2 : ℝ)^e)^8 := by
  push_cast
  rfl

theorem cast_inverse_power (e : ℕ) : ((1/((2^e : ℕ) : ℚ) : ℚ) : ℝ) = ((2 : ℝ)^e)⁻¹ := by
  push_cast
  rw [one_div]

theorem spacingTest_real {e L d : ℕ} {K ε : ℚ} (h : SpacingTest e L K ε d) :
    ((2 : ℝ)^e)^8 ≤ (d : ℝ) ∧ ((2 : ℝ)^e)^4*(L : ℝ) ≤ (d : ℝ)^15 ∧
    (alpha L d : ℝ) ≤ 1 ∧ ((2 : ℝ)^e)^4*(L : ℝ)^12*(zeta d : ℝ) ≤ (ε : ℝ)/2^24 ∧
    ((2 : ℝ)^e)^4*(L : ℝ)^12*(zeta d : ℝ)^2 ≤
      (alpha L d : ℝ)*(ε : ℝ)/(2^24*(K : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast h.spacing
  · exact_mod_cast h.fifteenth
  · exact_mod_cast h.alpha_le
  · exact_mod_cast h.first
  · exact_mod_cast h.second

end Maxwell.Continuum.Parameters
