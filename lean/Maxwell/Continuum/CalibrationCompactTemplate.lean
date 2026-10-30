import Maxwell.Continuum.CalibrationCompactFourier
import Maxwell.Continuum.CalibrationSupercellCoefficients
import Maxwell.Continuum.CompactTemplateRealReady

/-! Exact passage from a finite supercell coefficient array to the
compact source/test template, followed by real tensor encoding. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber MeasureTheory Profile FiniteAuxiliary EffectiveMass

variable (M : ℕ) [NeZero M] {B : ℕ}

theorem finiteData_outside (v : FourierData) (n : Alias)
    (hn : n∉PeriodicSampling.Product.frequencyCube v.radius) : v.value n=0 :=
  fieldValue_zero v.supported n hn

theorem idealTemplateField_scaled_identity (hEven : Even M) (L : ℚ)
    (hL : 1≤(L : ℝ)) (hM : 16*((L : ℝ)+1)≤(M : ℝ))
    (v : FourierData) (a : Alias→Fin 3→ComplexDyadic B)
    (ha : ∀n∈PeriodicSampling.Product.frequencyCube v.radius, ∀i,
      complexDyadicValue (a n i)=v.value n i) (r : Space) :
    (physicalFactor M : ℂ) •
      idealTemplateField (PeriodicSampling.Product.frequencyCube v.radius)
        (templateFrequency M L) a (zero_lt_one.trans_le hL) r=
      siteInsertion (L : ℝ)⁻¹ r (embedding M v.value) := by
  have hL0 : L≠0 := by
    intro hz
    rw [hz,Rat.cast_zero] at hL
    norm_num at hL
  apply PiLp.ext
  intro i
  apply Lp.ext
  simp only [PiLp.smul_apply]
  filter_upwards [Lp.coeFn_smul (physicalFactor M : ℂ)
      (idealTemplateField (PeriodicSampling.Product.frequencyCube v.radius)
        (templateFrequency M L) a (zero_lt_one.trans_le hL) r i),
    idealTemplateField_ae (PeriodicSampling.Product.frequencyCube v.radius)
      (templateFrequency M L) a (zero_lt_one.trans_le hL) r i,
    siteInsertion_embedding_finite_ae M hEven hL hM
      (PeriodicSampling.Product.frequencyCube v.radius) v.value (finiteData_outside v) r i]
    with x hsm hi hs
  rw [hsm]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hi,hs]
  unfold idealPlacedTemplate idealFiniteTemplate finiteFourier
  have hf : (∑n∈PeriodicSampling.Product.frequencyCube v.radius,
      complexDyadicValue (a n i)*spatialPlaneWave (templateFrequency M L n)
        (fun k => ((L : ℝ)⁻¹ • (x-r)) k))=
      ∑n∈PeriodicSampling.Product.frequencyCube v.radius,
        UnitAddTorus.mFourier n (torusPoint M (x-r))*v.value n i := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [ha n hn i]
    change v.value n i*spatialPlaneWave (templateFrequency M L n)
      (fun k => (L : ℝ)⁻¹*(x-r) k)=_
    rw [templateFrequency_character M L hL0]
    exact mul_comm _ _
  rw [hf]
  ring

theorem idealTemplateField_physicalSeries (hEven : Even M) (L : ℚ)
    (hL : 1≤(L : ℝ)) (hM : 16*((L : ℝ)+1)≤(M : ℝ))
    (v : FourierData) (a : Alias→Fin 3→ComplexDyadic B)
    (ha : ∀n∈PeriodicSampling.Product.frequencyCube v.radius, ∀i,
      complexDyadicValue (a n i)=v.value n i) (r : Space) :
    idealTemplateField (PeriodicSampling.Product.frequencyCube v.radius)
      (templateFrequency M L) a (zero_lt_one.trans_le hL) r=
      siteInsertion (L : ℝ)⁻¹ r (physicalSeriesField M v) := by
  rw [physicalSeriesField,map_smul,
    ← idealTemplateField_scaled_identity M hEven L hL hM v a ha r,
    smul_smul,inv_mul_cancel₀,one_smul]
  exact_mod_cast (physicalFactor_pos M).ne'

theorem idealTemplateField_mode_error (hEven : Even M) (L : ℚ)
    (hL : 1≤(L : ℝ)) (hM : 16*((L : ℝ)+1)≤(M : ℝ))
    (v : FourierData) (a : Alias→Fin 3→ComplexDyadic B)
    (ha : ∀n∈PeriodicSampling.Product.frequencyCube v.radius, ∀i,
      complexDyadicValue (a n i)=v.value n i) (r : Space) (f : FieldL2) :
    ‖idealTemplateField (PeriodicSampling.Product.frequencyCube v.radius)
      (templateFrequency M L) a (zero_lt_one.trans_le hL) r-
      siteInsertion (L : ℝ)⁻¹ r f‖≤‖physicalSeriesField M v-f‖ := by
  rw [idealTemplateField_physicalSeries M hEven L hL hM v a ha,← map_sub]
  simpa only [one_mul] using
    (siteInsertion (L : ℝ)⁻¹ r).le_of_opNorm_le (siteInsertion_norm _ _) (physicalSeriesField M v-f)

theorem realTemplate_mode_certificate (hEven : Even M) (L : ℚ)
    (hL : 1≤(L : ℝ)) (hM : 16*((L : ℝ)+1)≤(M : ℝ))
    (v : FourierData) (a : Alias→Fin 3→ComplexDyadic B)
    (ha : ∀n∈PeriodicSampling.Product.frequencyCube v.radius, ∀i,
      complexDyadicValue (a n i)=v.value n i) (Q N ell A : ℕ)
    (hRQ : |L| * (v.radius : ℚ)≤2*(M : ℚ)*Q)
    (hsize : (L : ℝ)≤(2 : ℝ)^ell)
    (hmass : templateCoefficientMass (PeriodicSampling.Product.frequencyCube v.radius) a≤(2 : ℝ)^A)
    {z δ : ℝ} (D : Auxiliary.Calibration (L : ℝ)⁻¹ z)
    (hh : (L : ℝ)⁻¹≤1/(2 : ℝ)^1024) (r : Space)
    (hmode : ‖physicalSeriesField M v-realMode D hh‖≤δ)
    (hsmall : δ+(1/2 : ℝ)^(N+20)≤1) :
    let f := realEncodedTemplateField (PeriodicSampling.Product.frequencyCube v.radius)
      (templateFrequency M L) a Q (N+2*ell+A) (zero_lt_one.trans_le hL) r
    fieldConjugation f=f ∧ ‖f‖≤2 ∧
      (∀k, ∀ᵐx∂(volume : Measure Space), x∉Metric.ball r (L : ℝ) → f k x=0) ∧
      ‖f-siteInsertion (L : ℝ)⁻¹ r (realMode D hh)‖≤δ+(1/2 : ℝ)^(N+20) := by
  apply realEncodedTemplate_site_certificate _ _ _ Q N ell A
    (fun n hn i => templateFrequency_bound M L v.radius Q hRQ hn i)
    hL hsize hmass D hh r _ hsmall
  exact (idealTemplateField_mode_error M hEven L hL hM v a ha r _).trans hmode

#print axioms idealTemplateField_physicalSeries
#print axioms realTemplate_mode_certificate

end Maxwell.Continuum.Calibration.Supercell
