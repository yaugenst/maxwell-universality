import Maxwell.Continuum.CellBandFourierMomentum
import Maxwell.Continuum.EffectiveMassDenominator
import Maxwell.Continuum.WellFourierDecay
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact angular Fourier phases and broad-well Fourier scaling. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open FreeFiber CellBandFourier MeasureTheory FourierTransform

def angularPhase (p x : Space) : ℂ := Complex.exp ((inner ℝ p x : ℂ) * Complex.I)

theorem angularPhase_norm (p x : Space) : ‖angularPhase p x‖ = 1 := by
  rw [angularPhase, Complex.norm_exp]
  simp

theorem angularPhase_continuous (p : Space) : Continuous (angularPhase p) := by
  unfold angularPhase
  fun_prop

theorem angularPhase_add (p q x : Space) :
    angularPhase (p+q) x = angularPhase p x * angularPhase q x := by
  simp only [angularPhase, inner_add_left, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem angularPhase_star (p x : Space) : star (angularPhase p x) = angularPhase (-p) x := by
  rw [angularPhase, Complex.star_def, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, angularPhase,
    inner_neg_left, Complex.ofReal_neg, neg_mul, mul_neg]

theorem angularPhase_smul (a : ℝ) (p x : Space) :
    angularPhase p (a • x) = angularPhase (a • p) x := by
  simp only [angularPhase, real_inner_smul_right, real_inner_smul_left]

theorem spatialPhase_physical (p x : Space) : spatialPhase (physicalMomentum p) x = angularPhase p x := by
  simp only [spatialPhase, physicalMomentum, realMomentum, angularPhase, PiLp.inner_apply,
    RCLike.inner_apply, starRingEnd_apply, star_trivial, Complex.ofReal_sum, Complex.ofReal_mul,
    mul_comm (x _ : ℂ)]
  congr 1
  ring

def aliasFrequency (q : Space) (ν : Alias) : Space :=
  q + Bloch.corner + Real.pi • Bloch.integerVector ν

theorem aliasFrequency_momentum (q : Space) (ν : Alias) :
    physicalMomentum (aliasFrequency q ν) = aliasMomentum (physicalMomentum q) ν := by
  funext j
  simp only [physicalMomentum, realMomentum, aliasFrequency, PiLp.add_apply,
    PiLp.smul_apply, Bloch.corner, Bloch.integerVector_apply,
    aliasMomentum, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_intCast, smul_eq_mul]
  ring

theorem aliasFrequency_sub (q r : Space) (ν μ : Alias) :
    aliasFrequency q ν - aliasFrequency r μ = q-r + Real.pi • Bloch.integerVector (ν-μ) := by
  apply PiLp.ext
  intro j
  simp only [aliasFrequency, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    Bloch.integerVector_apply, Pi.sub_apply, Int.cast_sub, smul_eq_mul]
  ring

theorem rawPhysicalFourier_eq_integral (p : Space) :
    Well.rawPhysicalFourier Well.w p = ∫ x, (Well.w x : ℂ) * angularPhase (-p) x := by
  rw [Well.rawPhysicalFourier, Real.fourier_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [Well.complexify, angularPhase, real_inner_smul_right, inner_neg_left,
      real_inner_comm x p, Complex.ofReal_neg, smul_eq_mul]
    rw [mul_comm (Well.w x : ℂ)]
    congr 1
    congr 1
    push_cast
    field_simp

theorem scaled_well_integrable {h : ℝ} (hh : 0 < h) :
    Integrable (fun x : Space => Well.w (h • x)) :=
  Well.w_integrable.comp_smul hh.ne'

theorem modulated_scaled_well_integrable {h : ℝ} (hh : 0 < h) (p : Space) :
    Integrable (fun x => (Well.w (h • x) : ℂ) * angularPhase p x) := by
  apply (scaled_well_integrable hh).mono'
  · have hw : Continuous (fun x : Space => Well.w (h • x)) :=
      Well.w_contDiff.continuous.comp (continuous_const_smul h)
    exact ((Complex.continuous_ofReal.comp hw).mul (angularPhase_continuous p)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [norm_mul, angularPhase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Well.w_nonneg _)]

theorem scaled_well_phase_integral {h : ℝ} (hh : 0 < h) (p : Space) :
    (∫ x, (Well.w (h • x) : ℂ) * angularPhase (-p) x) =
      (h^3)⁻¹ • Well.rawPhysicalFourier Well.w (h⁻¹ • p) := by
  rw [rawPhysicalFourier_eq_integral]
  have hs := Measure.integral_comp_smul_of_nonneg (volume : Measure Space)
    (fun x => (Well.w x : ℂ) * angularPhase (-(h⁻¹ • p)) x) h (hR := hh.le)
  rw [show Module.finrank ℝ Space = 3 from finrank_euclideanSpace_fin] at hs
  have hp (x : Space) : angularPhase (-(h⁻¹ • p)) (h • x) = angularPhase (-p) x := by
    rw [angularPhase_smul, smul_neg, smul_smul, mul_inv_cancel₀ hh.ne', one_smul]
  simpa only [hp] using hs

#print axioms aliasFrequency_momentum
#print axioms scaled_well_phase_integral

end Maxwell.Continuum.EffectiveMass
