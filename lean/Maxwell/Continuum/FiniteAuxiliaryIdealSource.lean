import Maxwell.Continuum.FiniteAuxiliaryLocalSource
import Maxwell.Continuum.FiniteAuxiliaryPlacedH1
import Maxwell.Continuum.MasterConstants

/-! The actual ideal source, its finite-well formula, and its H¹ bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option exponentiation.threshold 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass Bloch FourierSobolev MeasureTheory MasterConstants

attribute [local irreducible] realMode Sh muH Qh

variable {ι : Type*} [Fintype ι]

def idealSource {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (r : ι → Space) (α : ℝ) (g : BrightSpace ι) : FieldL2 :=
  ((α/muH D hh : ℝ) : ℂ) • placedField r (localSource D hh) g

theorem idealSource_eq {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (r : ι → Space) (α : ℝ) (g : BrightSpace ι) :
    idealSource D hh r α g = ((α/muH D hh : ℝ) : ℂ) • insertion h r (bright (realMode D hh) g) := by
  unfold idealSource
  congr 1
  rw [insertion_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [bright_apply, siteInsertion, ContinuousLinearMap.comp_apply, map_smul,
    translationOperator_apply, localSource]

theorem muH_inverse_le {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) :
    (muH D hh)⁻¹ ≤ (2 : ℝ)^128*h^2 := by
  have hp := D.h_pos
  have hi := (inv_le_inv₀ (muH_pos D hh)
    (by positivity : 0 < (1/(2 : ℝ)^128)*(h^2)⁻¹)).mpr (muH_bounds D hh).1
  simpa only [mul_inv_rev, inv_inv, one_div, mul_comm] using hi

theorem idealSource_norm {h z α : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (r : ι → Space) (hα : 0 ≤ α)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (g : BrightSpace ι) : ‖idealSource D hh r α g‖ = (α/muH D hh)*‖localSource D hh‖*‖g‖ := by
  have hp := muH_pos D hh
  rw [idealSource, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    placedField_norm r h⁻¹ (localSource D hh) (localSource_supported D hh) hdisj g, mul_assoc]

theorem idealSource_norm_upper {h z α : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (r : ι → Space) (hα : 0 ≤ α)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (g : BrightSpace ι) : ‖idealSource D hh r α g‖ ≤ (2 : ℝ)^128*α*h^2*‖g‖ := by
  rw [idealSource_norm D hh r hα hdisj g]
  have hp := muH_pos D hh
  calc
    _ ≤ (α/muH D hh)*1*‖g‖ := by gcongr; exact localSource_norm_le D hh
    _ ≤ (α*((2 : ℝ)^128*h^2))*‖g‖ := by
      rw [mul_one, div_eq_mul_inv]
      gcongr
      exact muH_inverse_le D hh
    _ = _ := by ring

def idealSourceH1 {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (r : ι → Space) (α : ℝ) (g : BrightSpace ι) : H1Data (idealSource D hh r α g) :=
  (placedH1 r (localSourceH1 D hh) g).smul ((α/muH D hh : ℝ) : ℂ)

theorem idealSourceH1_norm {h z α : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (r : ι → Space) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (g : BrightSpace ι) : (idealSourceH1 D hh r α g).norm ≤ (2 : ℝ)^700*‖g‖ := by
  have hp := muH_pos D hh
  have hhpos := D.h_pos
  have hn : 0 ≤ (localSourceH1 D hh).norm := Real.sqrt_nonneg _
  change ((placedH1 r (localSourceH1 D hh) g).smul ((α/muH D hh : ℝ) : ℂ)).norm ≤ _
  rw [H1Data_smul_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    placedH1_norm r h⁻¹ (localSourceH1 D hh) (localSource_supported D hh) hdisj g]
  calc
    _ ≤ (α*((2 : ℝ)^128*h^2))*(((2 : ℝ)^520*(h^2)⁻¹)*‖g‖) := by
      rw [div_eq_mul_inv]
      gcongr
      · exact muH_inverse_le D hh
      · exact localSourceH1_norm D hh
    _ = α*(2 : ℝ)^648*‖g‖ := by
      rw [show (2 : ℝ)^648 = 2^128*2^520 by rw [← pow_add]]
      field_simp
    _ ≤ (2 : ℝ)^700*‖g‖ := by
      gcongr
      calc
        α*(2 : ℝ)^648 ≤ 1*(2 : ℝ)^648 := mul_le_mul_of_nonneg_right hα1 (by positivity)
        _ ≤ (2 : ℝ)^700 := by norm_num

theorem idealSource_supported {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (r : ι → Space) (α : ℝ) (g : BrightSpace ι) (k : Fin 3) :
    ∀ᵐ x ∂volume, (∀ i, h⁻¹ ≤ ‖x-r i‖) → idealSource D hh r α g k x = 0 := by
  filter_upwards [placedField_supported r h⁻¹ (localSource D hh) (localSource_supported D hh) g k,
    Lp.coeFn_smul ((α/muH D hh : ℝ) : ℂ) (placedField r (localSource D hh) g k)] with x hx hs hdist
  change (((α/muH D hh : ℝ) : ℂ) • placedField r (localSource D hh) g k) x = 0
  rw [hs, Pi.smul_apply, hx hdist, smul_zero]

#print axioms idealSource_eq
#print axioms idealSourceH1_norm
#print axioms idealSource_supported

end Maxwell.Continuum.FiniteAuxiliary
