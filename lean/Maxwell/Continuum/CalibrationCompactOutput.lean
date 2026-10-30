import Maxwell.Continuum.CalibrationCompactTemplate
import Maxwell.Continuum.CalibrationCompactFrequency
import Maxwell.Continuum.CalibrationPhysicalRounding
import Maxwell.Continuum.RealTensorOutput

/-! The actual output encoder for a stored finite Fourier mode. Every
coefficient, frequency bound, and precision below is computed; only the
finite mode's proved approximation is consumed at the analytic boundary. -/

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber Profile MeasureTheory FiniteAuxiliary EffectiveMass

def compactNormalizationBits (N ellM : ℕ) : ℕ := N+3*ellM+7
def compactFourierBits (N ellM ellR : ℕ) : ℕ := N+3*ellM+3*ellR+9
def compactMassBits (ellR : ℕ) : ℕ := 3*ellR+5
def compactTensorBits (N ellL ellR : ℕ) : ℕ := N+2*ellL+compactMassBits ellR

def compactCoefficient (M N ellM ellR : ℕ) (v : FourierData) :=
  roundFourierCoefficient (compactFourierBits N ellM ellR)
    (physicalCoefficientData M (compactNormalizationBits N ellM) v)

def compactFourierData (M N ellM ellR : ℕ) (v : FourierData) : FourierData :=
  roundFourierData (compactFourierBits N ellM ellR)
    (physicalCoefficientData M (compactNormalizationBits N ellM) v)

def compactOutputBits (M : ℕ) (L : ℚ) (v : FourierData) (N ellM ellR ellL : ℕ) : List Bool :=
  realCompactBits (PeriodicSampling.Product.frequencyCube v.radius) (templateFrequency M L)
    (fun i n => compactCoefficient M N ellM ellR v n i)
    (templateFrequencyBound M L v.radius) (compactTensorBits N ellL ellR)

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

variable (M : ℕ) [NeZero M]

def compactTemplateField (L : ℚ) (v : FourierData) (N ellM ellR ellL : ℕ)
    (hL : 0<(L : ℝ)) (r : Space) : FieldL2 :=
  realEncodedTemplateField (PeriodicSampling.Product.frequencyCube v.radius) (templateFrequency M L)
    (compactCoefficient M N ellM ellR v) (templateFrequencyBound M L v.radius)
    (compactTensorBits N ellL ellR) hL r

omit [NeZero M] in
theorem compactTemplateField_ae (L : ℚ) (v : FourierData) (N ellM ellR ellL : ℕ)
    (hL : 0<(L : ℝ)) (r : Space) (i : Fin 3) :
    compactTemplateField M L v N ellM ellR ellL hL r i =ᵐ[volume] fun x =>
      (realEncodedPlacedTemplate (PeriodicSampling.Product.frequencyCube v.radius)
        (templateFrequency M L) (fun n => compactCoefficient M N ellM ellR v n i)
        (templateFrequencyBound M L v.radius) (compactTensorBits N ellL ellR) (L : ℝ) r x : ℂ) :=
  realEncodedTemplateField_ae _ _ _ _ _ _ _ _

omit [NeZero M] in
theorem compactFourierData_radius (N ellM ellR : ℕ) (v : FourierData) :
    (compactFourierData M N ellM ellR v).radius=v.radius := rfl

omit [NeZero M] in
theorem compactCoefficient_value (N ellM ellR : ℕ) (v : FourierData) (n : Alias) (i : Fin 3) :
    complexDyadicValue (compactCoefficient M N ellM ellR v n i)=
      (compactFourierData M N ellM ellR v).value n i :=
  roundFourierData_coordinate _ _ n i

theorem compactCoefficient_mass (N ellM ellR : ℕ) (v : FourierData) (hv : ‖v.value‖≤2)
    (hR : ((2*v.radius+1 : ℕ) : ℝ)≤(2 : ℝ)^ellR) :
    templateCoefficientMass (PeriodicSampling.Product.frequencyCube v.radius)
      (compactCoefficient M N ellM ellR v)≤(2 : ℝ)^compactMassBits ellR := by
  have hv' : ‖(physicalCoefficientData M (compactNormalizationBits N ellM) v).value‖≤4 :=
    (physicalCoefficientData_norm M _ v).trans (by linarith only [hv])
  have hc (n : Alias) (i : Fin 3) :
      ‖complexDyadicValue (compactCoefficient M N ellM ellR v n i)‖≤6 :=
    (roundFourierCoefficient_norm _ _ n i).trans (by linarith only [hv'])
  calc
    _ ≤ ∑ _i : Fin 3, ∑ _n∈PeriodicSampling.Product.frequencyCube v.radius,(6 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun n _ => hc n i)
    _ = 18*((2*v.radius+1 : ℕ) : ℝ)^3 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        PeriodicSampling.Product.frequencyCube_card,Nat.cast_pow]
      ring
    _ ≤ 32*((2 : ℝ)^ellR)^3 := by gcongr; norm_num
    _ = _ := by
      rw [compactMassBits,pow_add,← pow_mul]
      norm_num
      rw [Nat.mul_comm ellR 3]
      ring

theorem compactCoefficient_component_mass (N ellM ellR : ℕ) (v : FourierData)
    (hv : ‖v.value‖≤2) (hR : ((2*v.radius+1 : ℕ) : ℝ)≤(2 : ℝ)^ellR) (i : Fin 3) :
    (∑n∈PeriodicSampling.Product.frequencyCube v.radius,
      ‖complexDyadicValue (compactCoefficient M N ellM ellR v n i)‖)≤(2 : ℝ)^compactMassBits ellR := by
  apply le_trans _ (compactCoefficient_mass M N ellM ellR v hv hR)
  exact Finset.single_le_sum
    (f := fun k : Fin 3 => ∑n∈PeriodicSampling.Product.frequencyCube v.radius,
      ‖complexDyadicValue (compactCoefficient M N ellM ellR v n k)‖)
    (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ i)

theorem compactFourierData_error (N ellM ellR : ℕ) (v : FourierData) (f : FieldL2)
    (hv : ‖v.value‖≤2) (hM : (M : ℝ)≤(2 : ℝ)^ellM)
    (hR : ((2*v.radius+1 : ℕ) : ℝ)≤(2 : ℝ)^ellR)
    (he : ‖embedding M v.value-f‖≤(1/2 : ℝ)^(N+2)) :
    ‖physicalSeriesField M (compactFourierData M N ellM ellR v)-f‖≤(1/2 : ℝ)^(N+1) := by
  have hc := roundedPhysicalCoefficientData_error M (N+2) ellM ellR
    (compactNormalizationBits N ellM) (compactFourierBits N ellM ellR) v hv hM hR
    (by unfold compactNormalizationBits; omega) (by unfold compactFourierBits; omega)
  calc
    _ ≤ ‖physicalSeriesField M (compactFourierData M N ellM ellR v)-embedding M v.value‖+
        ‖embedding M v.value-f‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1/2 : ℝ)^(N+2)+(1/2 : ℝ)^(N+2) := add_le_add hc he
    _ = _ := by rw [pow_succ]; ring

theorem compactTemplate_certificate (hEven : Even M) (L : ℚ) (hL : 1≤(L : ℝ))
    (hgeometry : 16*((L : ℝ)+1)≤(M : ℝ)) (v : FourierData) (N ellM ellR ellL : ℕ)
    (hv : ‖v.value‖≤2) (hM : (M : ℝ)≤(2 : ℝ)^ellM)
    (hR : ((2*v.radius+1 : ℕ) : ℝ)≤(2 : ℝ)^ellR) (hsize : (L : ℝ)≤(2 : ℝ)^ellL)
    {z : ℝ} (D : Auxiliary.Calibration (L : ℝ)⁻¹ z)
    (hh : (L : ℝ)⁻¹≤1/(2 : ℝ)^1024)
    (he : ‖embedding M v.value-realMode D hh‖≤(1/2 : ℝ)^(N+2)) (r : Space) :
    let f := compactTemplateField M L v N ellM ellR ellL (zero_lt_one.trans_le hL) r
    fieldConjugation f=f ∧ ‖f‖≤2 ∧
      (∀k, ∀ᵐx∂(volume : Measure Space), x∉Metric.ball r (L : ℝ) → f k x=0) ∧
      ‖f-siteInsertion (L : ℝ)⁻¹ r (realMode D hh)‖≤(1/2 : ℝ)^N := by
  have hsum : (1/2 : ℝ)^(N+1)+(1/2 : ℝ)^(N+20)≤(1/2 : ℝ)^N := by
    have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)≤1)
      (show N+1≤N+20 by omega)
    calc
      _ ≤ (1/2 : ℝ)^(N+1)+(1/2 : ℝ)^(N+1) := add_le_add le_rfl hp
      _ = _ := by rw [pow_succ]; ring
  have hsmall := hsum.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hc := realTemplate_mode_certificate M hEven L hL hgeometry
    (compactFourierData M N ellM ellR v) (compactCoefficient M N ellM ellR v)
    (fun n _ i => compactCoefficient_value M N ellM ellR v n i)
    (templateFrequencyBound M L v.radius) N ellL (compactMassBits ellR)
    (templateFrequencyBound_spec M L v.radius) hsize
    (compactCoefficient_mass M N ellM ellR v hv hR) D hh r
    (compactFourierData_error M N ellM ellR v _ hv hM hR he) hsmall
  change fieldConjugation _=_ ∧ ‖_‖≤2 ∧ _ ∧ _ at hc
  exact ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.trans hsum⟩

theorem compactOutputBits_polylog (L : ℚ) (v : FourierData) (N ellM ellR ellL C ℓ : ℕ)
    (hv : ‖v.value‖≤2) (hR : ((2*v.radius+1 : ℕ) : ℝ)≤(2 : ℝ)^ellR)
    (hℓ : 0<ℓ) (hQ : templateFrequencyBound M L v.radius≤C*ℓ^8)
    (hT : compactTensorBits N ellL ellR≤C*ℓ)
    (hB : compactFourierBits N ellM ellR≤C*ℓ) (hA : compactMassBits ellR≤C*ℓ) :
    (compactOutputBits M L v N ellM ellR ellL).length≤realCompactBitsCoefficient C*ℓ^25 :=
  realCompactBits_polylog _ _ _ (fun _n hn i => templateFrequency_computed_bound M L v.radius hn i)
    (compactCoefficient_component_mass M N ellM ellR v hv hR) hℓ hQ hT hB hA

#print axioms compactTemplate_certificate
#print axioms compactOutputBits_polylog

end
end Maxwell.Continuum.Calibration.Supercell
