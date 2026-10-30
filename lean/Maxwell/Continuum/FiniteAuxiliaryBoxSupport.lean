import Maxwell.Continuum.FiniteAuxiliarySourceRegularity
import Maxwell.Continuum.BoxReferenceResidual

/-! Buffered physical wells supply every support premise in the actual
PEC reference-field residual, including support of weak derivatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass FourierSobolev MasterConstants Bloch CellGauge BoxCutoff MeasureTheory

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh

theorem localSource_eq_actualSource {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) : localSource D hh = actualSource D hh := rfl

variable {ι : Type*} [Fintype ι]

def idealCoefficients {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (α : ℝ) (g : BrightSpace ι) (i : ι) : ℂ := ((α/muH D hh : ℝ) : ℂ)*g i

theorem idealSource_sum {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (r : ι → Space) (α : ℝ) (g : BrightSpace ι) :
    idealSource D hh r α g = ∑ i, idealCoefficients D hh α g i •
      fieldTranslation (-r i) (actualSource D hh) := by
  rw [idealSource, placedField, localSource_eq_actualSource, Finset.smul_sum]
  simp only [idealCoefficients, smul_smul]

omit [Fintype ι] in
theorem idealCoefficients_norm_le {h z α : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (hα : 0 ≤ α) (hα1 : α ≤ 1) (g : BrightSpace ι) (i : ι) :
    ‖idealCoefficients D hh α g i‖ ≤ ‖g i‖ := by
  have hμ := muH_pos D hh
  have hsmall : (2 : ℝ)^128*h^2 ≤ 1 := by
    calc
      _ ≤ (2 : ℝ)^128*(1/(2 : ℝ)^1024)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ D.h_pos.le hh 2) (by positivity)
      _ ≤ 1 := by
        rw [div_pow, one_pow, mul_one_div]
        apply (div_le_one (by positivity : (0 : ℝ) < ((2 : ℝ)^1024)^2)).mpr
        rw [← pow_mul]
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hμi : (muH D hh)⁻¹ ≤ 1 := (muH_inverse_le D hh).trans hsmall
  have hc : α/muH D hh ≤ 1 := by
    rw [div_eq_mul_inv]
    exact (mul_le_mul hα1 hμi (inv_nonneg.mpr hμ.le) zero_le_one).trans_eq (mul_one 1)
  rw [idealCoefficients, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)

theorem idealSource_interior {L z b : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (n : Fin 3 → ℕ) (hb : 0 ≤ b) (r : ι → Space)
    (hr : ∀ i j, b+L+8 ≤ r i j ∧ r i j ≤ side n j-b-L-8)
    (α : ℝ) (g : BrightSpace ι) :
    familyProjection (interiorCells n b) (idealSource D (inverse_length_le_1024 hL) r α g) =
      idealSource D (inverse_length_le_1024 hL) r α g := by
  apply well_support_interior n hb r hr
  intro j
  simpa only [inv_inv] using idealSource_supported D (inverse_length_le_1024 hL) r α g j

theorem solvedSource_interior {L z σ b : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64) (n : Fin 3 → ℕ) (hb : 0 ≤ b)
    (r : ι → Space) (hr : ∀ i j, b+L+8 ≤ r i j ∧ r i j ≤ side n j-b-L-8)
    (v : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (α : ℝ) (g : BrightSpace ι) :
    familyProjection (interiorCells n b)
      (auxiliarySource D hσ0 hσ r A (idealSource D (inverse_length_le_1024 hL) r α g)) =
      auxiliarySource D hσ0 hσ r A (idealSource D (inverse_length_le_1024 hL) r α g) := by
  apply well_support_interior n hb r hr
  intro j
  simpa only [inv_inv] using auxiliarySource_supported D hσ0 hσ r v hv A hA
    (idealSource_supported D (inverse_length_le_1024 hL) r α g) j

theorem solvedSource_derivative_interior {L z σ b : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64) (n : Fin 3 → ℕ) (hb : 0 ≤ b)
    (r : ι → Space) (hr : ∀ i j, b+L+8 ≤ r i j ∧ r i j ≤ side n j-b-L-8)
    (v : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (α : ℝ) (g : BrightSpace ι)
    (Df : H1Data (auxiliarySource D hσ0 hσ r A (idealSource D (inverse_length_le_1024 hL) r α g)))
    (j : Fin 3) : familyProjection (interiorCells n b) (Df.derivative j) = Df.derivative j := by
  apply well_support_interior n hb r hr
  intro k
  simpa only [inv_inv] using auxiliarySource_derivative_supported D hσ0 hσ r v hv A hA
    (idealSource_supported D (inverse_length_le_1024 hL) r α g) Df j k

#print axioms solvedSource_interior
#print axioms solvedSource_derivative_interior

end Maxwell.Continuum.FiniteAuxiliary
