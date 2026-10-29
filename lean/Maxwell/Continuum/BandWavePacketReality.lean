import Maxwell.Continuum.BandWavePacketSection

/-! The normalized Fourier section is real at real momentum, so its
bilinear projection is the usual Hermitian rank-one projection there. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.BandWavePacket

open FreeFiber FiberNormalization PeriodicBand
open scoped ComplexOrder

theorem normalize_real_formula (v : FiberSpace) (hv : star v = v) :
    normalize v = (‖v‖ : ℂ)⁻¹ • v := by
  have hsq : (0 : ℂ) ≤ ((‖v‖ ^ 2 : ℝ) : ℂ) := by exact_mod_cast sq_nonneg ‖v‖
  simp only [FiberNormalization.normalize, multiplier, bilinear_self_real v hv,
    Complex.sqrt_of_nonneg hsq, Complex.ofReal_re, Real.sqrt_sq (norm_nonneg v)]

theorem normalize_star_of_real (v : FiberSpace) (hv : star v = v) :
    star (normalize v) = normalize v := by
  have hsq : (0 : ℂ) ≤ ((‖v‖ ^ 2 : ℝ) : ℂ) := by exact_mod_cast sq_nonneg ‖v‖
  have hs : Complex.sqrt (bilinear v v) = ((Real.sqrt (‖v‖ ^ 2) : ℝ) : ℂ) := by
    rw [bilinear_self_real v hv, Complex.sqrt_of_nonneg hsq, Complex.ofReal_re]
  simp only [FiberNormalization.normalize, multiplier, star_smul, star_inv₀, hs, hv,
    Complex.star_def, Complex.conj_ofReal]

theorem normalizedFiberVector_star_real (t : Fin 3 → ℝ) (ht : realMomentum t ∈ chart) :
    star (normalizedFiberVector (realMomentum t)) = normalizedFiberVector (realMomentum t) :=
  normalize_star_of_real _ (fiberVector_real t ht)

theorem sectionValue_star (q : Bloch.QuasiCell) : star (sectionValue q) = sectionValue q := by
  by_cases hq : q ∈ region
  · rw [sectionValue_eq hq, parameter_real]
    apply normalizedFiberVector_star_real
    rwa [← parameter_real]
  · rw [sectionValue_zero hq, star_zero]

theorem sectionValue_bilinear_inner (q : Bloch.QuasiCell) (v : FiberSpace) :
    bilinear (sectionValue q) v = inner ℂ (sectionValue q) v := by
  rw [bilinear_apply, sectionValue_star]

#print axioms normalizedFiberVector_star_real
#print axioms sectionValue_bilinear_inner

end Maxwell.Continuum.BandWavePacket
