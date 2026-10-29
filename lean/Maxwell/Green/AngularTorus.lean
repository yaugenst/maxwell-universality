import Maxwell.Defect.TorusChart
import Maxwell.Green.ChartVolume
import Maxwell.Green.PeriodicRemainder

/-! Exact angular coordinates for the normalized Bloch torus. -/

noncomputable section

open MeasureTheory Set WithLp

namespace Maxwell.Green

def angularTorusPoint (q : RealTorusCoordinates) : UnitAddTorus (Fin 3) :=
  fun i => (q i / (2 * Real.pi) : ℝ)

theorem continuous_angularTorusPoint : Continuous angularTorusPoint := by
  unfold angularTorusPoint
  fun_prop

theorem angularTorusPoint_eq_momentumTorus (q : RealTorusCoordinates) :
    angularTorusPoint q = Maxwell.Defect.TorusChart.momentumTorus (toLp 2 q) := by
  ext i
  simp only [angularTorusPoint, Maxwell.Defect.TorusChart.momentumTorus,
    Maxwell.Defect.TorusChart.quotient, PiLp.smul_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

/-- The coordinate identification preserves the actual angular cube
measure, including its half-open boundary convention. -/
theorem angularCube_toLp_measurePreserving :
    MeasurePreserving (toLp 2 : RealTorusCoordinates → MomentumSpace)
      (torusCubeMeasure (-Real.pi) (2 * Real.pi))
      (volume.restrict Maxwell.Defect.TorusChart.physicalCell) := by
  have h := (PiLp.volume_preserving_toLp (Fin 3)).restrict_preimage
    Maxwell.Defect.TorusChart.measurableSet_physicalCell
  have he : (toLp 2 : RealTorusCoordinates → MomentumSpace) ⁻¹'
      Maxwell.Defect.TorusChart.physicalCell = Set.univ.pi
        (fun _ : Fin 3 => Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)) := by
    ext q
    simp only [mem_preimage, Maxwell.Defect.TorusChart.physicalCell, mem_ofPred_eq,
      Set.mem_pi, mem_univ, forall_const, mem_Ioc,
      show -Real.pi + 2 * Real.pi = Real.pi by ring]
  rw [he] at h
  rwa [torusCubeMeasure_eq_restrict]

theorem integral_angularCube_toLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : MomentumSpace → E) :
    (∫ q, f (toLp 2 q) ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)) =
      ∫ q in Maxwell.Defect.TorusChart.physicalCell, f q :=
  angularCube_toLp_measurePreserving.integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding f

/-- The normalized Haar integral is exactly the angular cube integral
with the physical `(2π)⁻³` normalization. -/
theorem integral_angularTorus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UnitAddTorus (Fin 3) → E)
    (hf : AEStronglyMeasurable f Maxwell.Defect.TorusChart.haar) :
    (∫ t, f t ∂Maxwell.Defect.TorusChart.haar) =
      (1 / (2 * Real.pi) ^ 3 : ℝ) •
        ∫ q, f (angularTorusPoint q) ∂torusCubeMeasure (-Real.pi) (2 * Real.pi) := by
  rw [Maxwell.Defect.TorusChart.integral_physicalCell f hf,
    ← integral_angularCube_toLp]
  simp only [angularTorusPoint_eq_momentumTorus]

theorem integral_centered_angularTorus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UnitAddTorus (Fin 3) → E)
    (hf : AEStronglyMeasurable f Maxwell.Defect.TorusChart.haar)
    (center : UnitAddTorus (Fin 3)) :
    (∫ t, f t ∂Maxwell.Defect.TorusChart.haar) =
      (1 / (2 * Real.pi) ^ 3 : ℝ) •
        ∫ q, f (center + angularTorusPoint q)
          ∂torusCubeMeasure (-Real.pi) (2 * Real.pi) := by
  rw [Maxwell.Defect.TorusChart.integral_centered_physicalCell f hf center,
    ← integral_angularCube_toLp]
  simp only [angularTorusPoint_eq_momentumTorus]

theorem integral_angularTorus_complex
    (f : UnitAddTorus (Fin 3) → ℂ)
    (hf : AEStronglyMeasurable f Maxwell.Defect.TorusChart.haar) :
    (∫ t, f t ∂Maxwell.Defect.TorusChart.haar) =
      ((2 * Real.pi : ℂ) ^ 3)⁻¹ *
        ∫ q, f (angularTorusPoint q) ∂torusCubeMeasure (-Real.pi) (2 * Real.pi) := by
  rw [integral_angularTorus f hf, Complex.real_smul]
  simp only [one_div, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_ofNat]

theorem integral_centered_angularTorus_complex
    (f : UnitAddTorus (Fin 3) → ℂ)
    (hf : AEStronglyMeasurable f Maxwell.Defect.TorusChart.haar)
    (center : UnitAddTorus (Fin 3)) :
    (∫ t, f t ∂Maxwell.Defect.TorusChart.haar) =
      ((2 * Real.pi : ℂ) ^ 3)⁻¹ *
        ∫ q, f (center + angularTorusPoint q)
          ∂torusCubeMeasure (-Real.pi) (2 * Real.pi) := by
  rw [integral_centered_angularTorus f hf center, Complex.real_smul]
  simp only [one_div, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_ofNat]

theorem integrable_angularTorus
    {E : Type*} [NormedAddCommGroup E]
    (f : UnitAddTorus (Fin 3) → E) (hf : Integrable f Maxwell.Defect.TorusChart.haar) :
    Integrable (fun q => f (angularTorusPoint q))
      (torusCubeMeasure (-Real.pi) (2 * Real.pi)) := by
  have hp := Maxwell.Defect.TorusChart.integrable_physicalCell f hf
  have h := angularCube_toLp_measurePreserving.integrable_comp_of_integrable hp
  simpa only [Function.comp_def, ← angularTorusPoint_eq_momentumTorus] using h

@[simp] theorem angularTorusPoint_periodic (q : RealTorusCoordinates) (i : Fin 3) :
    angularTorusPoint (q + (2 * Real.pi) • Pi.single i 1) = angularTorusPoint q := by
  ext j
  by_cases h : j = i
  · subst j
    simp only [angularTorusPoint, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one, add_div]
    rw [div_self (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
    exact AddCircle.coe_add_period 1 _
  · simp [angularTorusPoint, Pi.single_eq_of_ne h]

@[simp] theorem mFourier_angularTorusPoint (n : Fin 3 → ℤ) (q : RealTorusCoordinates) :
    UnitAddTorus.mFourier n (angularTorusPoint q) =
      Complex.exp (Complex.I * (integerPairingCLM n q : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, angularTorusPoint,
    fourier_coe_apply, Complex.ofReal_one, div_one, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have heq (j : Fin 3) :
      2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ) * ((q j : ℂ) / (2 * Real.pi)) =
      Complex.I * (n j : ℂ) * (q j : ℂ) := by field_simp
  simp_rw [heq]
  rw [← Complex.exp_sum]
  congr 1
  simp [integerPairingCLM_apply, Finset.mul_sum, mul_assoc]

@[simp] theorem mFourier_angularTorusPoint_direction
    (d : ℕ) (v : Fin 3 → ℤ) (q : RealTorusCoordinates) :
    UnitAddTorus.mFourier (fun i => (d : ℤ) * v i) (angularTorusPoint q) =
      torusFourierFactor d v q := by
  rw [mFourier_angularTorusPoint]
  unfold torusFourierFactor oscillatoryFactor
  congr 1
  simp only [integerPairingCLM_apply, Int.cast_mul, Int.cast_natCast,
    ← Finset.mul_sum, mul_assoc, Complex.ofReal_mul, Complex.ofReal_natCast]

theorem mFourier_momentumTorus (n : Fin 3 → ℤ) (q : MomentumSpace) :
    UnitAddTorus.mFourier n (Maxwell.Defect.TorusChart.momentumTorus q) =
      Complex.exp (Complex.I * ((∑ i, (n i : ℝ) * q i : ℝ) : ℂ)) := by
  have h := mFourier_angularTorusPoint n q.ofLp
  simpa only [angularTorusPoint_eq_momentumTorus, WithLp.toLp_ofLp,
    integerPairingCLM_apply] using h

end Maxwell.Green
