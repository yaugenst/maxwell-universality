import Maxwell.Green.TorusContour
import Maxwell.Green.PeriodicRemainder
import Maxwell.Green.TorusAsymptotic
import Maxwell.Green.Upper
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Whole-block contour deformation and its exponential bound. Scalar
contour invariance is lifted by the separating complex dual. -/

noncomputable section

namespace Maxwell.Green

open MeasureTheory Filter Set Complex
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [CompleteSpace V]

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem integrable_analytic_block_slice (φ : ComplexTorusCoordinates → V)
    (β : RealTorusCoordinates) (a p s : ℝ)
    (hφ : ∀ q ∈ torusCube a p, AnalyticAt ℂ φ (contourShift β s q)) :
    Integrable (fun q => φ (contourShift β s q)) (torusCubeMeasure a p) := by
  have hc : ContinuousOn (fun q => φ (contourShift β s q)) (torusCube a p) := by
    intro q hq
    exact ((hφ q hq).continuousAt.comp
      ((continuous_contourShift β).comp (continuous_const.prodMk continuous_id)).continuousAt).continuousWithinAt
  have hi := hc.integrableOn_compact (isCompact_torusCube a p) (μ := torusCubeMeasure a p)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_mem_torusCube a p)] at hi

theorem integral_analytic_periodic_block_contour_invariant
    (φ : ComplexTorusCoordinates → V) (β : RealTorusCoordinates)
    (a p : ℝ) (hp : 0 ≤ p)
    (hφ : AnalyticOnNhd ℂ φ (contourTube β a p))
    (hperiod : ∀ (i : Fin 3) (z : ComplexTorusCoordinates),
      φ (z + (p : ℂ) • Pi.single i 1) = φ z) :
    (∫ q, φ (complexifyCoordinates q + I • complexifyCoordinates β)
      ∂torusCubeMeasure a p) =
      ∫ q, φ (complexifyCoordinates q) ∂torusCubeMeasure a p := by
  have hs (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      Integrable (fun q => φ (contourShift β s q)) (torusCubeMeasure a p) :=
    integrable_analytic_block_slice φ β a p s
      (fun q hq => hφ _ ⟨(s, q), ⟨hs, hq⟩, rfl⟩)
  have hi₁ := hs 1 (by simp)
  have hi₀ := hs 0 (by simp)
  simp only [contourShift, one_smul, zero_smul, add_zero] at hi₁ hi₀
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)]
  intro L
  rw [← L.integral_comp_comm hi₁, ← L.integral_comp_comm hi₀]
  exact integral_analytic_periodic_contour_invariant (fun z => L (φ z)) β a p hp
    (fun z hz => (L.analyticAt _).comp (hφ z hz))
    (fun i z => congrArg L (hperiod i z))

def complexIntegerPairing (n : Fin 3 → ℤ) : ComplexTorusCoordinates →L[ℂ] ℂ :=
  ∑ i : Fin 3, (n i : ℂ) • ContinuousLinearMap.proj i

@[simp] theorem complexIntegerPairing_apply (n : Fin 3 → ℤ) (z : ComplexTorusCoordinates) :
    complexIntegerPairing n z = ∑ i, (n i : ℂ) * z i := by
  simp [complexIntegerPairing, smul_eq_mul]

@[simp] theorem complexIntegerPairing_real (n : Fin 3 → ℤ) (q : RealTorusCoordinates) :
    complexIntegerPairing n (complexifyCoordinates q) = (integerPairingCLM n q : ℂ) := by
  simp [complexIntegerPairing_apply, integerPairingCLM_apply, complexifyCoordinates]

@[simp] theorem complexIntegerPairing_single (n : Fin 3 → ℤ) (i : Fin 3) :
    complexIntegerPairing n (Pi.single i 1) = n i := by
  simp [complexIntegerPairing_apply, Pi.single_apply, mul_ite]

def complexFourierFactor (n : Fin 3 → ℤ) (z : ComplexTorusCoordinates) : ℂ :=
  Complex.exp (I * complexIntegerPairing n z)

theorem complexFourierFactor_analytic (n : Fin 3 → ℤ) (z : ComplexTorusCoordinates) :
    AnalyticAt ℂ (complexFourierFactor n) z :=
  (analyticAt_const.mul ((complexIntegerPairing n).analyticAt z)).cexp'

theorem complexFourierFactor_periodic (n : Fin 3 → ℤ) (i : Fin 3)
    (z : ComplexTorusCoordinates) :
    complexFourierFactor n (z + (2 * Real.pi : ℂ) • Pi.single i 1) =
      complexFourierFactor n z := by
  unfold complexFourierFactor
  rw [map_add, map_smul, complexIntegerPairing_single]
  have he : I * (complexIntegerPairing n z + (2 * Real.pi : ℂ) • (n i : ℂ)) =
      I * complexIntegerPairing n z + (n i : ℂ) * (2 * Real.pi * I) := by
    simp only [smul_eq_mul]
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem complexFourierFactor_shift (n : Fin 3 → ℤ) (β q : RealTorusCoordinates) :
    complexFourierFactor n (complexifyCoordinates q + I • complexifyCoordinates β) =
      shiftedFourierFactor (integerPairingCLM n q) (integerPairingCLM n β) := by
  simp [complexFourierFactor, shiftedFourierFactor, map_add, map_smul, smul_eq_mul,
    complexifyCoordinates]

/-- The true shifted representation for a whole operator or matrix block.
The original Fourier coefficient is the integral on the real torus. -/
theorem block_fourier_contour_identity
    (R : ComplexTorusCoordinates → V) (n : Fin 3 → ℤ) (β : RealTorusCoordinates)
    (hR : AnalyticOnNhd ℂ R (contourTube β (-Real.pi) (2 * Real.pi)))
    (hperiod : ∀ (i : Fin 3) (z : ComplexTorusCoordinates),
      R (z + (2 * Real.pi : ℂ) • Pi.single i 1) = R z) :
    (∫ q, complexFourierFactor n (complexifyCoordinates q) • R (complexifyCoordinates q)
      ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)) =
    ∫ q, shiftedFourierFactor (integerPairingCLM n q) (integerPairingCLM n β) •
      R (complexifyCoordinates q + I • complexifyCoordinates β)
      ∂torusCubeMeasure (-Real.pi) (2 * Real.pi) := by
  have h := integral_analytic_periodic_block_contour_invariant
    (fun z => complexFourierFactor n z • R z) β (-Real.pi) (2 * Real.pi)
    (by positivity) (fun z hz => (complexFourierFactor_analytic n z).smul (hR z hz))
    (fun i z => by
      push_cast
      rw [complexFourierFactor_periodic, hperiod])
  simpa only [complexFourierFactor_shift] using h.symm

/-- The actual whole-block Fourier coefficient has the shifted exponential
bound, with contour deformation proved rather than supplied. -/
theorem block_fourier_exponential_bound
    (R : ComplexTorusCoordinates → V) (n : Fin 3 → ℤ) (β : RealTorusCoordinates)
    (hR : AnalyticOnNhd ℂ R (contourTube β (-Real.pi) (2 * Real.pi)))
    (hperiod : ∀ (i : Fin 3) (z : ComplexTorusCoordinates),
      R (z + (2 * Real.pi : ℂ) • Pi.single i 1) = R z)
    (C : ℝ) (hb : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
      ‖R (complexifyCoordinates q + I • complexifyCoordinates β)‖ ≤ C) :
    ‖∫ q, complexFourierFactor n (complexifyCoordinates q) • R (complexifyCoordinates q)
      ∂torusCubeMeasure (-Real.pi) (2 * Real.pi)‖ ≤
      (torusCubeMeasure (-Real.pi) (2 * Real.pi)).real univ * C *
        Real.exp (-integerPairingCLM n β) := by
  rw [block_fourier_contour_identity R n β hR hperiod]
  exact norm_integral_shiftedFourier_le _ _ _ _
    ((ae_mem_torusCube (-Real.pi) (2 * Real.pi)).mono fun q hq => hb q hq)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [CompleteSpace V] in
theorem torusCubeMeasure_real_univ (a p : ℝ) (hp : 0 ≤ p) :
    (torusCubeMeasure a p).real univ = p ^ 3 := by
  simp [Measure.real, torusCubeMeasure, Measure.pi_univ, Real.volume_Ioc, hp]

/-- Fourier normalization cancels the fundamental cube volume exactly. -/
theorem normalized_block_fourier_exponential_bound
    (R : ComplexTorusCoordinates → V) (n : Fin 3 → ℤ) (β : RealTorusCoordinates)
    (hR : AnalyticOnNhd ℂ R (contourTube β (-Real.pi) (2 * Real.pi)))
    (hperiod : ∀ (i : Fin 3) (z : ComplexTorusCoordinates),
      R (z + (2 * Real.pi : ℂ) • Pi.single i 1) = R z)
    (C : ℝ) (hb : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
      ‖R (complexifyCoordinates q + I • complexifyCoordinates β)‖ ≤ C) :
    ‖((2 * Real.pi : ℂ) ^ 3)⁻¹ •
      (∫ q, complexFourierFactor n (complexifyCoordinates q) • R (complexifyCoordinates q)
        ∂torusCubeMeasure (-Real.pi) (2 * Real.pi))‖ ≤
      C * Real.exp (-integerPairingCLM n β) := by
  have h := block_fourier_exponential_bound R n β hR hperiod C hb
  rw [torusCubeMeasure_real_univ _ _ (by positivity)] at h
  rw [norm_smul, norm_inv, norm_pow]
  have hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    norm_cast
    simp [abs_of_pos Real.pi_pos]
  rw [hn]
  calc
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((2 * Real.pi) ^ 3 * C *
        Real.exp (-integerPairingCLM n β)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

/-- Constructing the maximizing admissible shift gives the complete block
bound in the inverse square-root metric, directly for the real Fourier
integral of the original analytic block family. -/
theorem block_ellipsoid_fourier_upper
    (R : ComplexTorusCoordinates → V) (n : Fin 3 → ℤ)
    (P Q : MomentumSpace →L[ℝ] MomentumSpace) (hQP : ∀ x, Q (P x) = x)
    (hsym : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (C : ℝ)
    (hR : ∀ β : MomentumSpace, ‖Q β‖ ≤ ρ →
      AnalyticOnNhd ℂ R (contourTube β.ofLp (-Real.pi) (2 * Real.pi)))
    (hperiod : ∀ (i : Fin 3) (z : ComplexTorusCoordinates),
      R (z + (2 * Real.pi : ℂ) • Pi.single i 1) = R z)
    (hb : ∀ β : MomentumSpace, ‖Q β‖ ≤ ρ →
      ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
        ‖R (complexifyCoordinates q + I • complexifyCoordinates β.ofLp)‖ ≤ C) :
    ‖((2 * Real.pi : ℂ) ^ 3)⁻¹ •
      (∫ q, complexFourierFactor n (complexifyCoordinates q) • R (complexifyCoordinates q)
        ∂torusCubeMeasure (-Real.pi) (2 * Real.pi))‖ ≤
      C * Real.exp (-ρ * ‖P (integerMomentum n)‖) := by
  let β := ellipsoidSupportPoint P ρ (integerMomentum n)
  have hβ : ‖Q β‖ ≤ ρ := ellipsoidSupportPoint_admissible P Q hQP ρ hρ _
  have hp : integerPairingCLM n β.ofLp = ρ * ‖P (integerMomentum n)‖ := by
    rw [← integerMomentum_inner, real_inner_comm]
    exact ellipsoidSupportPoint_pairing P hsym ρ _
  have h := normalized_block_fourier_exponential_bound R n β.ofLp (hR β hβ) hperiod C (hb β hβ)
  simpa only [hp, neg_mul] using h

end Maxwell.Green
