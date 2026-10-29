import Maxwell.Continuum.EffectiveMassFourierInverseHilbert
import Maxwell.Continuum.EffectiveMassKernelPhase
import Maxwell.Continuum.AngularFourier

/-! The actual unitary angular Fourier inverse equals its normalized
Bochner integral for every L¹∩L² Hilbert-valued amplitude. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FourierTransform

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem dilation_symm_eq {a : ℝ} (ha : 0 < a) (u : L2Dilation.L2 (H := H)) :
    (L2Dilation.equiv ha).symm u = L2Dilation.action (inv_pos.mpr ha) u := by
  apply (L2Dilation.equiv ha).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change u = L2Dilation.action ha (L2Dilation.action (inv_pos.mpr ha) u)
  simpa only [inv_inv] using (L2Dilation.action_inverse (inv_pos.mpr ha) u).symm

theorem dilation_inverse_integrable {a : ℝ} (ha : 0 < a) (u : L2Dilation.L2 (H := H))
    (hu : Integrable (fun p => u p)) :
    Integrable (fun p => L2Dilation.action (inv_pos.mpr ha) u p) := by
  apply ((hu.comp_smul ha.ne').smul (L2Dilation.factor a⁻¹ : ℂ)).congr
  change (fun x => (L2Dilation.factor a⁻¹ : ℂ) • u (a • x)) =ᵐ[volume]
    fun p => L2Dilation.action (inv_pos.mpr ha) u p
  simpa only [inv_inv] using (L2Dilation.action_ae (inv_pos.mpr ha) u).symm

theorem dilation_inverse_factor {a : ℝ} (ha : 0 < a) :
    L2Dilation.factor a⁻¹ * (a^3)⁻¹ = L2Dilation.factor a := by
  have hs := Real.sq_sqrt (pow_pos ha 3).le
  have hn := (Real.sqrt_pos.mpr (pow_pos ha 3)).ne'
  simp only [L2Dilation.factor, inv_pow, Real.sqrt_inv, inv_inv]
  field_simp
  nlinarith

theorem angularFourier_inverse_integral [CompleteSpace H] (u : L2Dilation.L2 (H := H))
    (hu : Integrable (fun p => u p)) :
    (angularFourier H).symm u =ᵐ[volume] fun x =>
      (((2 * Real.pi) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) •
        ∫ p, angularPhase p x • u p := by
  have ha : 0 < 2 * Real.pi := by positivity
  have he : (angularFourier H).symm u =
      (𝓕⁻ (L2Dilation.action (inv_pos.mpr ha) u) : L2Dilation.L2 (H := H)) := by
    change (𝓕⁻ ((L2Dilation.equiv ha).symm u) : L2Dilation.L2 (H := H)) = _
    rw [dilation_symm_eq]
  rw [he]
  filter_upwards [fourierInvL2_ae_integral_hilbert
    (L2Dilation.action (inv_pos.mpr ha) u) (dilation_inverse_integrable ha u hu)] with x hx
  rw [hx, Real.fourierInv_congr_ae (L2Dilation.action_ae (inv_pos.mpr ha) u) x,
    Real.fourierInv_eq']
  simp only [inv_inv]
  have hphase (p : Space) : Complex.exp (((2 * Real.pi * inner ℝ p x : ℝ) : ℂ) * Complex.I) =
      angularPhase ((2 * Real.pi) • p) x := by
    simp only [angularPhase, real_inner_smul_left]
  simp only [hphase, smul_comm _ (L2Dilation.factor (2 * Real.pi)⁻¹ : ℂ), integral_smul]
  have hi := Measure.integral_comp_smul_of_nonneg (volume : Measure Space)
    (fun p => angularPhase p x • u p) (2 * Real.pi) (hR := ha.le)
  rw [show Module.finrank ℝ Space = 3 from finrank_euclideanSpace_fin] at hi
  rw [hi]
  have hreal (r : ℝ) (v : H) : r • v = (r : ℂ) • v := by
    change r • v = (algebraMap ℝ ℂ r) • v
    exact (algebraMap_smul ℂ r v).symm
  rw [hreal, smul_smul, ← Complex.ofReal_mul, dilation_inverse_factor ha,
    angularFourier_factor]

#print axioms angularFourier_inverse_integral

end Maxwell.Continuum.EffectiveMass
