import Maxwell.Green.UniformContour
import Maxwell.Green.BlockContour
import Maxwell.Green.TorusAsymptotic

/-! The singular boundary shift for the actual Fourier coefficient,
including its exact exponential decay factor. -/

noncomputable section

namespace Maxwell.Green

open Filter Set MeasureTheory
open scoped Topology

theorem scalar_boundary_fourier_identity
    (R : ComplexTorusCoordinates → ℂ) (n : Fin 3 → ℤ) (β : RealTorusCoordinates)
    (hσ : 0 ≤ integerPairingCLM n β)
    (hR : ∀ t ∈ Ico (0 : ℝ) 1, AnalyticOnNhd ℂ R
      (contourTube (t • β) (-Real.pi) (2 * Real.pi)))
    (hperiod : ∀ (i : Fin 3) (z : ComplexTorusCoordinates),
      R (z + (2 * Real.pi : ℂ) • Pi.single i 1) = R z)
    (hboundary : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      ContinuousAt R (contourShift β 1 q))
    (C : ℝ)
    (hbound : ∀ t ∈ Ico (0 : ℝ) 1, ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      ‖R (contourShift β t q)‖ ≤ coordinateBoundaryMajorant C q) :
    (∫ q, complexFourierFactor n (complexifyCoordinates q) * R (complexifyCoordinates q)
      ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)) =
      (Real.exp (-integerPairingCLM n β) : ℂ) *
        ∫ q, complexFourierFactor n (complexifyCoordinates q) * R (contourShift β 1 q)
          ∂torusCubeMeasure (-Real.pi) (2 * Real.pi) := by
  let φ := fun z => complexFourierFactor n z * R z
  have hφboundary : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      ContinuousAt φ (contourShift β 1 q) := by
    intro q hq hq₀
    exact (complexFourierFactor_analytic n _).continuousAt.mul (hboundary q hq hq₀)
  have hm : AEStronglyMeasurable (fun q => φ (contourShift β 1 q))
      (torusCubeMeasure (-Real.pi) (2 * Real.pi)) := by
    apply aestronglyMeasurable_of_continuousAt_punctured_cube
    intro q hq hq₀
    exact (hφboundary q hq hq₀).comp
      ((continuous_contourShift β).continuousAt.comp (continuousAt_const.prodMk continuousAt_id))
  have hb : ∀ t ∈ Ico (0 : ℝ) 1, ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      ‖φ (contourShift β t q)‖ ≤ coordinateBoundaryMajorant C q := by
    intro t ht q hq hq₀
    have hn : ‖complexFourierFactor n (contourShift β t q)‖ ≤ 1 := by
      rw [contourShift_rescale, complexFourierFactor_shift, norm_shiftedFourierFactor,
        map_smul, smul_eq_mul]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht.1 hσ))
    exact (norm_mul _ _).trans_le
      ((mul_le_of_le_one_left (norm_nonneg _) hn).trans (hbound t ht q hq hq₀))
  obtain ⟨_, hid⟩ := analytic_periodic_boundary_contour_identity φ
    (fun q => φ (contourShift β 1 q)) β C (-Real.pi) (2 * Real.pi) (by positivity)
    (fun t ht z hz => (complexFourierFactor_analytic n z).mul (hR t ht z hz))
    (fun i z => by
      change complexFourierFactor n _ * R _ = _
      push_cast
      rw [complexFourierFactor_periodic, hperiod]) hm hb
    (fun q hq hq₀ => tendsto_contourShift_value φ β q (hφboundary q hq hq₀))
  rw [hid, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  have he : complexFourierFactor n (contourShift β 1 q) =
      (Real.exp (-integerPairingCLM n β) : ℂ) *
        complexFourierFactor n (complexifyCoordinates q) := by
    simp only [contourShift, one_smul, complexFourierFactor, map_add, map_smul,
      smul_eq_mul]
    rw [show Complex.I * (complexIntegerPairing n (complexifyCoordinates q) +
      Complex.I * complexIntegerPairing n (complexifyCoordinates β)) =
        -(integerPairingCLM n β : ℂ) +
          Complex.I * complexIntegerPairing n (complexifyCoordinates q) by
        simp only [complexIntegerPairing_real]
        linear_combination (integerPairingCLM n β : ℂ) * Complex.I_sq]
    rw [Complex.exp_add, ← Complex.ofReal_neg, Complex.ofReal_exp]
  change complexFourierFactor n (contourShift β 1 q) * R (contourShift β 1 q) = _
  rw [he]
  ring

@[simp] theorem integerPairingCLM_nat_mul
    (d : ℕ) (v : Fin 3 → ℤ) (q : RealTorusCoordinates) :
    integerPairingCLM (fun i => (d : ℤ) * v i) q =
      (d : ℝ) * integerPairingCLM v q := by
  simp only [integerPairingCLM_apply, Int.cast_mul, Int.cast_natCast,
    Finset.mul_sum, mul_assoc]

@[simp] theorem complexFourierFactor_nat_mul_real
    (d : ℕ) (v : Fin 3 → ℤ) (q : RealTorusCoordinates) :
    complexFourierFactor (fun i => (d : ℤ) * v i) (complexifyCoordinates q) =
      torusFourierFactor d v q := by
  simp only [complexFourierFactor, complexIntegerPairing_real,
    integerPairingCLM_nat_mul, Complex.ofReal_mul, Complex.ofReal_natCast,
    torusFourierFactor, oscillatoryFactor, mul_assoc]

/-- The boundary shift for the integer ray `d * v`, with the exact physical
decay factor and the real torus Fourier phase. -/
theorem scalar_boundary_fourier_identity_direction
    (R : ComplexTorusCoordinates → ℂ) (v : Fin 3 → ℤ) (β : RealTorusCoordinates)
    (hσ : 0 ≤ integerPairingCLM v β)
    (hR : ∀ t ∈ Ico (0 : ℝ) 1, AnalyticOnNhd ℂ R
      (contourTube (t • β) (-Real.pi) (2 * Real.pi)))
    (hperiod : ∀ (i : Fin 3) (z : ComplexTorusCoordinates),
      R (z + (2 * Real.pi : ℂ) • Pi.single i 1) = R z)
    (hboundary : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      ContinuousAt R (contourShift β 1 q))
    (C : ℝ)
    (hbound : ∀ t ∈ Ico (0 : ℝ) 1, ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      ‖R (contourShift β t q)‖ ≤ coordinateBoundaryMajorant C q)
    (d : ℕ) :
    (∫ q, torusFourierFactor d v q * R (complexifyCoordinates q)
      ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)) =
      (Real.exp (-integerPairingCLM v β * (d : ℝ)) : ℂ) *
        ∫ q, torusFourierFactor d v q * R (contourShift β 1 q)
          ∂torusCubeMeasure (-Real.pi) (2 * Real.pi) := by
  have hd : 0 ≤ integerPairingCLM (fun i => (d : ℤ) * v i) β := by
    rw [integerPairingCLM_nat_mul]
    exact mul_nonneg (Nat.cast_nonneg d) hσ
  simpa only [complexFourierFactor_nat_mul_real, integerPairingCLM_nat_mul,
    neg_mul, mul_comm (d : ℝ)] using
    scalar_boundary_fourier_identity R (fun i => (d : ℤ) * v i) β hd
      hR hperiod hboundary C hbound

namespace TorusLocalAssemblyData

/-- The saddle-derived full scalar Green function is the normalized Fourier
coefficient on the original real torus. The singular boundary shift is proved
from the contour hypotheses, rather than supplied as an integral identity. -/
theorem fullScalarGreen_eq_real_fourier
    {v : Fin 3 → ℤ} (D : TorusLocalAssemblyData v)
    (R : ComplexTorusCoordinates → ℂ) (β : RealTorusCoordinates)
    (hσ : 0 ≤ integerPairingCLM v β)
    (hR : ∀ t ∈ Ico (0 : ℝ) 1, AnalyticOnNhd ℂ R
      (contourTube (t • β) (-Real.pi) (2 * Real.pi)))
    (hperiod : ∀ (i : Fin 3) (z : ComplexTorusCoordinates),
      R (z + (2 * Real.pi : ℂ) • Pi.single i 1) = R z)
    (hboundary : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      ContinuousAt R (contourShift β 1 q))
    (C : ℝ)
    (hbound : ∀ t ∈ Ico (0 : ℝ) 1, ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      ‖R (contourShift β t q)‖ ≤ coordinateBoundaryMajorant C q)
    (hH : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      D.H q = R (contourShift β 1 q))
    (d : ℕ) :
    D.fullScalarGreen 0 (integerPairingCLM v β) d =
      ((2 * Real.pi : ℂ) ^ 3)⁻¹ *
        ∫ q, torusFourierFactor d v q * R (complexifyCoordinates q)
          ∂torusCubeMeasure (-Real.pi) (2 * Real.pi) := by
  have hnull : NullSingletonClass (torusCubeMeasure (-Real.pi) (2 * Real.pi)) := by
    unfold torusCubeMeasure
    infer_instance
  have heq : (∫ q, torusFourierFactor d v q * D.H q
      ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)) =
      ∫ q, torusFourierFactor d v q * R (contourShift β 1 q)
        ∂torusCubeMeasure (-Real.pi) (2 * Real.pi) := by
    apply integral_congr_ae
    filter_upwards [ae_mem_torusCube (-Real.pi) (2 * Real.pi),
      (torusCubeMeasure (-Real.pi) (2 * Real.pi)).ae_ne 0] with q hq hq₀
    rw [hH q hq hq₀]
  rw [scalar_boundary_fourier_identity_direction R v β hσ hR hperiod hboundary C hbound d,
    fullScalarGreen, normalizedTorusGreen, heq]
  simp only [scalarShiftFactor, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_exp]
  simp only [neg_mul]
  ring

end TorusLocalAssemblyData

end Maxwell.Green
