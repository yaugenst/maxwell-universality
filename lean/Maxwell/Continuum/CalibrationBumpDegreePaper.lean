import Maxwell.Continuum.CalibrationBumpDegree

/-! The concrete computed degree fits the displayed torus/well scale
bound from the continuum calibration construction. -/

namespace Maxwell.Continuum.Calibration

open MasterConstants

theorem rootDegree_paper_bound (L M : ℚ) (hL : 0 < L) (hM : 2*L ≤ M) (N ell : ℕ) :
    (rootDegree (2*M/L) N (ell+1) : ℝ) ≤
      Cs^4*(1+(M : ℝ)/(L : ℝ))*((N+ell+2 : ℕ) : ℝ)^2 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hMr : 2*(L : ℝ) ≤ M := by exact_mod_cast hM
  have hm0 : 0 ≤ (M : ℝ)/(L : ℝ) := div_nonneg (by linarith) hLr.le
  have hs : (4 : ℝ) ≤ ((2*M/L : ℚ) : ℝ) := by
    push_cast
    exact (le_div_iff₀ hLr).mpr (by linarith)
  have hu := rootDegree_upper (2*M/L) hs N (ell+1)
  have hx : (((N+(ell+1)+2 : ℕ) : ℝ)) ≤ 2*((N+ell+2 : ℕ) : ℝ) := by push_cast; linarith
  have hC : (16 : ℝ) ≤ Cs := by
    have h := fixed_power_le_Cs (n := 4) (by have := exponent_large; omega)
    norm_num at h
    exact h
  have hCs0 := Cs_pos
  calc
    _ ≤ 2*Cs^3*(((2*M/L : ℚ) : ℝ))*((N+(ell+1)+2 : ℕ) : ℝ)^2 := hu
    _ ≤ 2*Cs^3*(((2*M/L : ℚ) : ℝ))*(2*((N+ell+2 : ℕ) : ℝ))^2 := by gcongr
    _ = (16*Cs^3)*((M : ℝ)/(L : ℝ))*((N+ell+2 : ℕ) : ℝ)^2 := by push_cast; ring
    _ ≤ (Cs*Cs^3)*((M : ℝ)/(L : ℝ))*((N+ell+2 : ℕ) : ℝ)^2 := by gcongr
    _ ≤ Cs^4*(1+(M : ℝ)/(L : ℝ))*((N+ell+2 : ℕ) : ℝ)^2 := by
      rw [← pow_succ']
      gcongr
      linarith

#print axioms rootDegree_paper_bound

end Maxwell.Continuum.Calibration
