import Maxwell.Defect.PowerRefinement
import Maxwell.Defect.SimpleCertificate

/-! Rational filter parameters obtained from a strict finite residual and
gap certificate. Their convergence factor is bounded away from one. -/
namespace Maxwell.Defect
open InnerProductSpace Module.End

def filterLower (gap bound : ℚ) : ℚ := 1 - gap ^ 2 / (16 * bound ^ 2)
def filterUpper (gap bound : ℚ) : ℚ := 1 - gap ^ 2 / (4 * bound ^ 2)

theorem filter_parameter_range (gap bound : ℚ) (hg : 0 < gap) (hM : 0 < bound)
    (hgM : gap ≤ bound) :
    0 ≤ filterUpper gap bound ∧ filterUpper gap bound < filterLower gap bound ∧
      1 / 2 ≤ filterLower gap bound ∧ filterLower gap bound ≤ 1 := by
  have hM2 := sq_pos_of_pos hM
  have hg2 := sq_pos_of_pos hg
  have hsq := pow_le_pow_left₀ hg.le hgM 2
  have h16 : gap ^ 2 / (16 * bound ^ 2) ≤ 1 / 16 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have h4 : gap ^ 2 / (4 * bound ^ 2) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hlt : gap ^ 2 / (16 * bound ^ 2) < gap ^ 2 / (4 * bound ^ 2) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  dsimp only [filterUpper, filterLower]
  have hnonneg : 0 ≤ gap ^ 2 / (16 * bound ^ 2) := by positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem scalarModeFilter_range (target bound x : ℝ) (hM : 0 < bound)
    (hx : |x - target| ≤ bound) :
    0 ≤ scalarModeFilter target (bound ^ 2)⁻¹ x ∧
      scalarModeFilter target (bound ^ 2)⁻¹ x ≤ 1 := by
  have hh := pow_le_pow_left₀ (abs_nonneg _) hx 2
  rw [sq_abs] at hh
  have hd : (x - target) ^ 2 / bound ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hM)).mpr hh
  dsimp only [scalarModeFilter]
  rw [← div_eq_inv_mul]
  constructor
  · linarith
  · have : 0 ≤ (x - target) ^ 2 / bound ^ 2 := by positivity
    linarith

theorem scalarModeFilter_selected (target bound gap μ : ℝ) (_hM : 0 < bound)
    (_hg : 0 ≤ gap) (hμ : |μ - target| ≤ gap / 4) :
    1 - gap ^ 2 / (16 * bound ^ 2) ≤ scalarModeFilter target (bound ^ 2)⁻¹ μ := by
  have hh := pow_le_pow_left₀ (abs_nonneg _) hμ 2
  rw [sq_abs] at hh
  have hd := div_le_div_of_nonneg_right hh (sq_nonneg bound)
  dsimp only [scalarModeFilter]
  rw [← div_eq_inv_mul]
  have he : (gap / 4) ^ 2 / bound ^ 2 = gap ^ 2 / (16 * bound ^ 2) := by ring
  rw [he] at hd
  linarith

theorem scalarModeFilter_complement (target bound gap x : ℝ) (hM : 0 < bound)
    (hg : 0 ≤ gap) (hxM : |x - target| ≤ bound) (hxg : gap / 2 ≤ |x - target|) :
    |scalarModeFilter target (bound ^ 2)⁻¹ x| ≤ 1 - gap ^ 2 / (4 * bound ^ 2) := by
  rw [abs_of_nonneg (scalarModeFilter_range target bound x hM hxM).1]
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ gap / 2) hxg 2
  rw [sq_abs] at hh
  have hd := div_le_div_of_nonneg_right hh (sq_nonneg bound)
  dsimp only [scalarModeFilter]
  rw [← div_eq_inv_mul]
  have he : (gap / 2) ^ 2 / bound ^ 2 = gap ^ 2 / (4 * bound ^ 2) := by ring
  rw [he] at hd
  linarith

section Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem eigenvalue_abs_le_norm (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) : |hS.eigenvalues rfl i| ≤ ‖S‖ := by
  have hh := S.le_opNorm ((hS.eigenvectorBasis rfl) i)
  have he : S ((hS.eigenvectorBasis rfl) i) =
      hS.eigenvalues rfl i • (hS.eigenvectorBasis rfl) i := hS.apply_eigenvectorBasis rfl i
  simpa only [he, norm_smul, (hS.eigenvectorBasis rfl).orthonormal.norm_eq_one i,
    mul_one, Real.norm_eq_abs] using hh

theorem modeFilter_norm_of_bound (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (target bound : ℝ) (hM : 0 < bound) (hnorm : ‖S‖ + |target| ≤ bound) :
    ‖modeFilter S target (bound ^ 2)⁻¹‖ ≤ 1 := by
  apply modeFilter_norm_le_one S hS
  intro i
  have hh : |hS.eigenvalues rfl i - target| ≤ bound :=
    (abs_sub _ _).trans ((add_le_add (eigenvalue_abs_le_norm S hS i) (le_refl |target|)).trans hnorm)
  obtain ⟨hlo, hhi⟩ := scalarModeFilter_range target bound _ hM hh
  rwa [abs_of_nonneg hlo]

end Spectral
end Maxwell.Defect
