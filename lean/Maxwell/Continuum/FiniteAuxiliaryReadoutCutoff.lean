import Maxwell.Continuum.FiniteAuxiliaryReadout
import Maxwell.Continuum.FiniteAuxiliaryBoxSupport

/-! The physical PEC cutoff preserves every ideal observable exactly:
all translated templates lie in its literal unit plateau. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.SchwartzMultiplier

open MeasureTheory
open scoped ComplexConjugate

theorem field_symmetric_of_real (θ : SchwartzMap Space ℂ) (hθ : ∀ x, conj (θ x) = θ x)
    (f g : FieldL2) : inner ℂ (field θ f) g = inner ℂ f (field θ g) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [field_ae θ f j, field_ae θ g j] with x hf hg
  rw [hf, hg]
  simp only [← smul_eq_mul, inner_smul_left, inner_smul_right, hθ]

end Maxwell.Continuum.SchwartzMultiplier

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass FourierSobolev MasterConstants Bloch CellGauge BoxCutoff
open MeasureTheory SchwartzMultiplier

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh

variable {ι : Type*} [Fintype ι]

theorem siteInsertion_actualSource {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (r : Space) :
    siteInsertion h r (realMode D hh) = fieldTranslation (-r) (actualSource D hh) := rfl

omit [Fintype ι] in
theorem siteInsertion_interior {L z b : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (n : Fin 3 → ℕ) (hb : 0 ≤ b) (r : ι → Space)
    (hr : ∀ i j, b+L+8 ≤ r i j ∧ r i j ≤ side n j-b-L-8) (i : ι) :
    familyProjection (interiorCells n b) (siteInsertion L⁻¹ (r i) (realMode D (inverse_length_le_1024 hL))) =
      siteInsertion L⁻¹ (r i) (realMode D (inverse_length_le_1024 hL)) := by
  rw [siteInsertion_actualSource]
  apply well_support_interior n hb r hr
  intro j
  have hs : ∀ᵐ x ∂volume, x ∉ Metric.ball (r i) L →
      fieldTranslation (-r i) (actualSource D (inverse_length_le_1024 hL)) j x = 0 := by
    apply translated_supported_ball
    intro k
    simpa only [inv_inv] using actualSource_supported D (inverse_length_le_1024 hL) k
  filter_upwards [hs] with x hx hdist
  exact hx (by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hdist i)

omit [Fintype ι] in
theorem idealReadout_cutoff {L z b : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (n : Fin 3 → ℕ) (hb : 0 ≤ b) (r : ι → Space)
    (hr : ∀ i j, b+L+8 ≤ r i j ∧ r i j ≤ side n j-b-L-8) (v : ι → ℝ) (f : FieldL2) :
    idealReadout L⁻¹ r v (realMode D (inverse_length_le_1024 hL)) (field (schwartz (side n)) f) =
      idealReadout L⁻¹ r v (realMode D (inverse_length_le_1024 hL)) f := by
  apply PiLp.ext
  intro i
  rw [idealReadout_apply, idealReadout_apply,
    ← field_symmetric_of_real (schwartz (side n)) (fun x => by rw [schwartz_apply]; simp),
    cutoff_preserves_source n hb _ (siteInsertion_interior hL D n hb r hr i)]

theorem idealReadout_referenceField {L z σ b : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64) (n : Fin 3 → ℕ) (hb : 0 ≤ b)
    (r : ι → Space) (hr : ∀ i j, b+L+8 ≤ r i j ∧ r i j ≤ side n j-b-L-8)
    (v : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (f : FieldL2) :
    idealReadout L⁻¹ r v (realMode D (inverse_length_le_1024 hL))
      (referenceField D hσ0 hσ (side n) (auxiliarySource D hσ0 hσ r A f) : FieldL2) =
      brightResponse D (inverse_length_le_1024 hL) hσ0 hσ r A f := by
  change idealReadout L⁻¹ r v (realMode D (inverse_length_le_1024 hL))
    (field (schwartz (side n)) (auxiliaryField D hσ0 hσ r A f)) = _
  rw [idealReadout_cutoff hL D n hb r hr]
  exact idealReadout_auxiliaryField D (inverse_length_le_1024 hL) hσ0 hσ r v hv A hA f

#print axioms idealReadout_cutoff
#print axioms idealReadout_referenceField

end Maxwell.Continuum.FiniteAuxiliary
