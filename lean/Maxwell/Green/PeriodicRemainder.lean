import Maxwell.Green.TorusContour
import Maxwell.Green.SmoothRemainder

/-! Quadratic Fourier decay of a smooth three-dimensional periodic remainder. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Maxwell.Green

def coordinateDerivative (φ : RealTorusCoordinates → ℂ) (i : Fin 3)
    (q : RealTorusCoordinates) : ℂ := fderiv ℝ φ q (Pi.single i 1)

def integerPairingCLM (v : Fin 3 → ℤ) : RealTorusCoordinates →L[ℝ] ℝ :=
  ∑ j : Fin 3, (v j : ℝ) • ContinuousLinearMap.proj j

@[simp] theorem integerPairingCLM_apply (v : Fin 3 → ℤ) (q : RealTorusCoordinates) :
    integerPairingCLM v q = ∑ j, (v j : ℝ) * q j := by
  simp [integerPairingCLM, smul_eq_mul]

@[simp] theorem integerPairingCLM_single (v : Fin 3 → ℤ) (i : Fin 3) :
    integerPairingCLM v (Pi.single i 1) = v i := by
  simp [integerPairingCLM_apply, Pi.single_apply, mul_ite]

def torusFourierFactor (d : ℕ) (v : Fin 3 → ℤ) (q : RealTorusCoordinates) : ℂ :=
  oscillatoryFactor d (integerPairingCLM v q)

@[simp] theorem torusFourierFactor_norm (d : ℕ) (v : Fin 3 → ℤ) (q : RealTorusCoordinates) :
    ‖torusFourierFactor d v q‖ = 1 := oscillatoryFactor_norm _ _

theorem continuous_torusFourierFactor (d : ℕ) (v : Fin 3 → ℤ) :
    Continuous (torusFourierFactor d v) := by
  unfold torusFourierFactor oscillatoryFactor
  fun_prop

theorem hasDerivAt_insertNth_real (i : Fin 3) (q : Fin 2 → ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (i.insertNth t q : RealTorusCoordinates)) (Pi.single i 1) x := by
  apply hasDerivAt_pi.mpr
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with hj | ⟨k, hj⟩
  · subst j
    simp only [Fin.insertNth_apply_same, Pi.single_eq_same]
    exact hasDerivAt_id x
  · subst j
    simpa using hasDerivAt_const x (q k)

theorem hasDerivAt_integerPairing (v : Fin 3 → ℤ) (i : Fin 3) (q : Fin 2 → ℝ) (x : ℝ) :
    HasDerivAt (fun t => integerPairingCLM v (i.insertNth t q)) (v i : ℝ) x := by
  simpa only [Function.comp_def, integerPairingCLM_single v i] using
    (integerPairingCLM v).hasFDerivAt.comp_hasDerivAt x (hasDerivAt_insertNth_real i q x)

theorem hasDerivAt_torusFourierFactor
    (d : ℕ) (v : Fin 3 → ℤ) (i : Fin 3) (q : Fin 2 → ℝ) (x : ℝ) :
    HasDerivAt (fun t => torusFourierFactor d v (i.insertNth t q))
      (Complex.I * ((d : ℝ) * (v i : ℝ)) * torusFourierFactor d v (i.insertNth x q)) x := by
  have h := (oscillatoryFactor_hasDerivAt (d : ℝ) (integerPairingCLM v (i.insertNth x q))).scomp x
    (hasDerivAt_integerPairing v i q x)
  convert h using 1
  · rfl
  · simp only [torusFourierFactor, Complex.real_smul]
    ring

theorem torusFourierFactor_periodic
    (d : ℕ) (v : Fin 3 → ℤ) (i : Fin 3) (q : RealTorusCoordinates) :
    torusFourierFactor d v (q + (2 * Real.pi) • Pi.single i 1) = torusFourierFactor d v q := by
  unfold torusFourierFactor oscillatoryFactor
  rw [map_add, map_smul, integerPairingCLM_single]
  simp only [smul_eq_mul]
  have heq : Complex.I * (d : ℂ) * ((integerPairingCLM v q + 2 * Real.pi * (v i : ℝ) : ℝ) : ℂ) =
      Complex.I * (d : ℂ) * (integerPairingCLM v q : ℂ) +
        (((d : ℤ) * v i : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  simp only [Complex.ofReal_natCast]
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem insertNth_period_vector (i : Fin 3) (q : Fin 2 → ℝ) (a p : ℝ) :
    i.insertNth (a + p) q = i.insertNth a q + p • Pi.single i 1 := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩ <;> simp

/-- Equality of values on opposite faces, only over the closed transverse cube. -/
def TorusFaceMatches (φ : RealTorusCoordinates → ℂ) (i : Fin 3) : Prop :=
  ∀ q : Fin 2 → ℝ, (∀ j, q j ∈ Icc (-Real.pi) (-Real.pi + 2 * Real.pi)) →
    φ (i.insertNth (-Real.pi + 2 * Real.pi) q) = φ (i.insertNth (-Real.pi) q)

/-- Local smoothness on the compact cube, allowing singularities outside it. -/
def SmoothOnTorusCube (φ : RealTorusCoordinates → ℂ) : Prop :=
  ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), ContDiffAt ℝ ∞ φ q

theorem SmoothOnTorusCube.coordinateDerivative
    {φ : RealTorusCoordinates → ℂ} (hφ : SmoothOnTorusCube φ) (i : Fin 3) :
    SmoothOnTorusCube (coordinateDerivative φ i) := by
  intro q hq
  exact ((hφ q hq).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

theorem SmoothOnTorusCube.continuousOn
    {φ : RealTorusCoordinates → ℂ} (hφ : SmoothOnTorusCube φ) :
    ContinuousOn φ (torusCube (-Real.pi) (2 * Real.pi)) := by
  intro q hq
  exact (hφ q hq).continuousAt.continuousWithinAt

theorem continuousOn_integrable_torusCube
    {φ : RealTorusCoordinates → ℂ} {a p : ℝ}
    (hφ : ContinuousOn φ (torusCube a p)) : Integrable φ (torusCubeMeasure a p) := by
  have h := hφ.integrableOn_compact (isCompact_torusCube a p) (μ := torusCubeMeasure a p)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_mem_torusCube a p)] at h

theorem SmoothOnTorusCube.hasDerivAt_coordinate
    {φ : RealTorusCoordinates → ℂ} (hφ : SmoothOnTorusCube φ)
    (i : Fin 3) (q : Fin 2 → ℝ) (x : ℝ)
    (hx : i.insertNth x q ∈ torusCube (-Real.pi) (2 * Real.pi)) :
    HasDerivAt (fun t => φ (i.insertNth t q))
      (Maxwell.Green.coordinateDerivative φ i (i.insertNth x q)) x :=
  ((hφ _ hx).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_insertNth_real i q x)

/-- One actual integration by parts on the cube. Boundary cancellation uses
only matching opposite faces, not a globally periodic extension. -/
theorem torus_fourier_coordinate_integration_by_parts
    {φ : RealTorusCoordinates → ℂ} (hφ : SmoothOnTorusCube φ)
    (i : Fin 3) (hface : TorusFaceMatches φ i) (d : ℕ) (v : Fin 3 → ℤ) :
    (∫ q, torusFourierFactor d v q * coordinateDerivative φ i q
      ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)) =
      -(Complex.I * ((d : ℝ) * (v i : ℝ))) *
        (∫ q, torusFourierFactor d v q * φ q
          ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)) := by
  let e := torusFourierFactor d v
  let k : ℂ := Complex.I * ((d : ℝ) * (v i : ℝ))
  have hi₀ : Integrable (fun q => e q * φ q)
      (torusCubeMeasure (-Real.pi) (2 * Real.pi)) := continuousOn_integrable_torusCube
    ((continuous_torusFourierFactor d v).continuousOn.mul hφ.continuousOn)
  have hi₁ : Integrable (fun q => e q * coordinateDerivative φ i q)
      (torusCubeMeasure (-Real.pi) (2 * Real.pi)) := continuousOn_integrable_torusCube
    ((continuous_torusFourierFactor d v).continuousOn.mul
      (hφ.coordinateDerivative i).continuousOn)
  have hz : (∫ q, k * (e q * φ q) + e q * coordinateDerivative φ i q
      ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)) = 0 := by
    apply periodic_pi_flux_integral_eq_zero_ae i (by positivity : 0 ≤ 2 * Real.pi)
      (f := fun q => e q * φ q)
    · filter_upwards [ae_pi_interval_mem_closed_cube 2 (-Real.pi) (2 * Real.pi)] with q hq
      intro x hx
      have hab : -Real.pi ≤ -Real.pi + 2 * Real.pi := by linarith [Real.pi_pos]
      have hx' : x ∈ Icc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
        simpa only [uIcc_of_le hab] using hx
      have hm := insertNth_mem_torusCube hq i hx'
      convert (hasDerivAt_torusFourierFactor d v i q x).mul
        (hφ.hasDerivAt_coordinate i q x hm) using 1
      simp only [e, k, mul_assoc]
    · exact (hi₀.const_mul k).add hi₁
    · filter_upwards [ae_pi_interval_mem_closed_cube 2 (-Real.pi) (2 * Real.pi)] with q hq
      rw [hface q hq]
      change torusFourierFactor d v (i.insertNth (-Real.pi + 2 * Real.pi) q) * _ = _
      rw [insertNth_period_vector, torusFourierFactor_periodic]
  rw [integral_add (hi₀.const_mul k) hi₁, integral_const_mul] at hz
  change _ = -k * _
  linear_combination hz

/-- Two integrations by parts give quadratic decay from smoothness near the
cube and matching values and first derivatives on its opposite faces. -/
theorem smooth_torus_fourier_bound_of_matching_faces
    {φ : RealTorusCoordinates → ℂ} (hφ : SmoothOnTorusCube φ)
    (v : Fin 3 → ℤ) (i : Fin 3) (hvi : v i ≠ 0)
    (hface₀ : TorusFaceMatches φ i)
    (hface₁ : TorusFaceMatches (coordinateDerivative φ i) i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, 0 < d →
      ‖∫ q, torusFourierFactor d v q * φ q
        ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)‖ ≤ C / (d : ℝ) ^ 2 := by
  let φ₁ := coordinateDerivative φ i
  let φ₂ := coordinateDerivative φ₁ i
  have hφ₁ : SmoothOnTorusCube φ₁ := hφ.coordinateDerivative i
  have hφ₂ : SmoothOnTorusCube φ₂ := hφ₁.coordinateDerivative i
  obtain ⟨M, hM⟩ := ((isCompact_torusCube (-Real.pi) (2 * Real.pi)).image_of_continuousOn
    hφ₂.continuousOn).isBounded.exists_norm_le
  let B := max M 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbound : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), ‖φ₂ q‖ ≤ B := by
    intro q hq
    exact (hM _ (mem_image_of_mem _ hq)).trans (le_max_left _ _)
  let μ := torusCubeMeasure (-Real.pi) (2 * Real.pi)
  have hvi' : (v i : ℝ) ≠ 0 := by exact_mod_cast hvi
  refine ⟨B * μ.real univ / (v i : ℝ) ^ 2, by positivity, ?_⟩
  intro d hd
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hT : (d : ℝ) * (v i : ℝ) ≠ 0 := mul_ne_zero hd' hvi'
  have h₁ := torus_fourier_coordinate_integration_by_parts hφ i hface₀ d v
  have h₂ := torus_fourier_coordinate_integration_by_parts hφ₁ i hface₁ d v
  have heq : ‖∫ q, torusFourierFactor d v q * φ₂ q ∂μ‖ =
      ((d : ℝ) * (v i : ℝ)) ^ 2 * ‖∫ q, torusFourierFactor d v q * φ q ∂μ‖ := by
    change ‖∫ q, torusFourierFactor d v q * coordinateDerivative φ₁ i q ∂μ‖ = _
    rw [h₂, h₁, norm_mul, norm_mul]
    simp only [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [← mul_assoc, ← sq, ← abs_mul, sq_abs]
  have hnorm : ‖∫ q, torusFourierFactor d v q * φ₂ q ∂μ‖ ≤ B * μ.real univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards [ae_mem_torusCube (-Real.pi) (2 * Real.pi)] with q hq
    rw [norm_mul, torusFourierFactor_norm, one_mul]
    exact hbound q hq
  rw [heq] at hnorm
  calc
    ‖∫ q, torusFourierFactor d v q * φ q ∂μ‖ ≤
        B * μ.real univ / ((d : ℝ) * (v i : ℝ)) ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_ne_zero hT)).mpr
      simpa only [mul_comm] using hnorm
    _ = (B * μ.real univ / (v i : ℝ) ^ 2) / (d : ℝ) ^ 2 := by
      rw [mul_pow]
      field_simp

/-- A periodic function has periodic coordinate derivatives. This follows
by differentiating translation, without a periodic-derivative premise. -/
theorem coordinateDerivative_periodic
    {φ : RealTorusCoordinates → ℂ} {p : ℝ} (i : Fin 3)
    (hperiod : ∀ q : RealTorusCoordinates, φ (q + p • Pi.single i 1) = φ q) :
    ∀ q : RealTorusCoordinates,
      coordinateDerivative φ i (q + p • Pi.single i 1) = coordinateDerivative φ i q := by
  intro q
  have heq : (fun x => φ (x + p • Pi.single i 1)) = φ := funext hperiod
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := q) (p • Pi.single i 1)
  rw [heq] at h
  exact congrArg (fun L : RealTorusCoordinates →L[ℝ] ℂ => L (Pi.single i 1)) h.symm

theorem torusFaceMatches_of_periodic
    {φ : RealTorusCoordinates → ℂ} (i : Fin 3)
    (hperiod : ∀ q : RealTorusCoordinates,
      φ (q + (2 * Real.pi) • Pi.single i 1) = φ q) : TorusFaceMatches φ i := by
  intro q _
  rw [insertNth_period_vector, hperiod]

/-- A globally smooth coordinate-periodic amplitude has `d⁻²` Fourier decay
along every nonzero integer direction. All derivative and compactness bounds
are consequences, not assumptions. -/
theorem smooth_periodic_torus_fourier_bound
    (φ : RealTorusCoordinates → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hperiod : ∀ (i : Fin 3) (q : RealTorusCoordinates),
      φ (q + (2 * Real.pi) • Pi.single i 1) = φ q)
    (v : Fin 3 → ℤ) (hv : v ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, 0 < d →
      ‖∫ q, Complex.exp (Complex.I * (d : ℂ) * ((∑ j, (v j : ℝ) * q j : ℝ) : ℂ)) * φ q
        ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)‖ ≤ C / (d : ℝ) ^ 2 := by
  have hex : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hex
  have hlocal : SmoothOnTorusCube φ := fun q _ => hφ.contDiffAt
  obtain ⟨C, hC, hb⟩ := smooth_torus_fourier_bound_of_matching_faces hlocal v i hi
    (torusFaceMatches_of_periodic i (hperiod i))
    (torusFaceMatches_of_periodic i (coordinateDerivative_periodic i (hperiod i)))
  refine ⟨C, hC, ?_⟩
  intro d hd
  simpa only [torusFourierFactor, oscillatoryFactor, integerPairingCLM_apply,
    Complex.ofReal_natCast] using hb d hd

/-- A local singular subtraction need not be globally periodic. If the
result agrees with a periodic function near both opposite faces, then both
its values and its first coordinate derivative have the matching faces
required by the decay theorem. -/
theorem torusFaceMatches_of_periodic_face_germs
    {φ ψ : RealTorusCoordinates → ℂ} (i : Fin 3)
    (hperiod : ∀ q : RealTorusCoordinates,
      ψ (q + (2 * Real.pi) • Pi.single i 1) = ψ q)
    (hgerm : ∀ q : Fin 2 → ℝ,
      (∀ j, q j ∈ Icc (-Real.pi) (-Real.pi + 2 * Real.pi)) →
      φ =ᶠ[𝓝 (i.insertNth (-Real.pi) q)] ψ ∧
      φ =ᶠ[𝓝 (i.insertNth (-Real.pi + 2 * Real.pi) q)] ψ) :
    TorusFaceMatches φ i ∧ TorusFaceMatches (coordinateDerivative φ i) i := by
  have hface₀ := torusFaceMatches_of_periodic i hperiod
  have hface₁ := torusFaceMatches_of_periodic i (coordinateDerivative_periodic i hperiod)
  constructor
  · intro q hq
    exact (hgerm q hq).2.eq_of_nhds.trans ((hface₀ q hq).trans (hgerm q hq).1.eq_of_nhds.symm)
  · intro q hq
    have hl := congrArg (fun L : RealTorusCoordinates →L[ℝ] ℂ => L (Pi.single i 1))
      (hgerm q hq).1.fderiv_eq
    have hr := congrArg (fun L : RealTorusCoordinates →L[ℝ] ℂ => L (Pi.single i 1))
      (hgerm q hq).2.fderiv_eq
    exact hr.trans ((hface₁ q hq).trans hl.symm)

end Maxwell.Green
