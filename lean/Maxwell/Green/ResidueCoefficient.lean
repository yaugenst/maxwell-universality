import Maxwell.Green.ScalarAsymptotic

/-! Exact Fourier-normalized coefficient for a nonzero compressed
eigenprojector numerator. The normal gradient cancels from the coefficient. -/

noncomputable section

namespace Maxwell.Green

open Complex Real

theorem scalarLeadingCoefficient_of_projector_residue (D : LocalSaddleData)
    (A₀ : ℂ) {v q₁ q₂ ν : ℝ}
    (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hν : 0 < ν)
    (ha : D.amplitude0 = A₀ / (I * (v : ℂ))) :
    scalarLeadingCoefficient D v q₁ q₂ ν =
      A₀ / ((2 * π * ν * sqrt (q₁ * q₂) : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hv' : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hν' : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hν.ne'
  have hq' : ((sqrt (q₁ * q₂) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos hq₁ hq₂)).ne'
  unfold scalarLeadingCoefficient
  rw [ha]
  push_cast
  field_simp

/-- A positive scalar projector numerator gives a positive real leading
coefficient with the exact transverse determinant normalization. -/
theorem scalarLeadingCoefficient_positive (D : LocalSaddleData)
    {A₀ v q₁ q₂ ν : ℝ} (hA₀ : 0 < A₀)
    (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hν : 0 < ν)
    (ha : D.amplitude0 = (A₀ : ℂ) / (I * (v : ℂ))) :
    (scalarLeadingCoefficient D v q₁ q₂ ν).im = 0 ∧
      0 < (scalarLeadingCoefficient D v q₁ q₂ ν).re := by
  rw [scalarLeadingCoefficient_of_projector_residue D A₀ hv hq₁ hq₂ hν ha,
    ← Complex.ofReal_div]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  positivity

end Maxwell.Green
