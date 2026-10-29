import Maxwell.Continuum.EffectiveMassKernelSeries
import Maxwell.Continuum.AliasSeparation

/-! The exact spatial Gram integral of two Bloch waves in the dilated well.
Every pair of Fourier aliases remains in the resulting kernel. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open FreeFiber CellBandFourier MeasureTheory

theorem weightedAliasGram_integral {h : ℝ} (hh : 0 < h)
    (q r : Space) (u v : FiberSpace) (a : Alias × Alias) :
    (∫ x, weightedAliasGram h q r u v a x) =
      (h^3)⁻¹ • (inner ℂ (u a.1) (v a.2) * Well.rawPhysicalFourier Well.w
        (h⁻¹ • (aliasFrequency q a.1 - aliasFrequency r a.2))) := by
  have heq : weightedAliasGram h q r u v a = fun x =>
      ((Well.w (h • x) : ℂ) *
        angularPhase (-(aliasFrequency q a.1 - aliasFrequency r a.2)) x) *
          inner ℂ (u a.1) (v a.2) := by
    funext x
    rw [weightedAliasGram, aliasGram_phase]
    ring
  rw [heq, integral_mul_const, scaled_well_phase_integral hh]
  simp only [Algebra.smul_def]
  ring

theorem weighted_blochField_gram {h : ℝ} (hh : 0 < h)
    (q r : Space) (u v : FiberSpace)
    (hu : Summable (fun ν => ‖u ν‖)) (hv : Summable (fun ν => ‖v ν‖)) :
    (∫ x, (Well.w (h • x) : ℂ) *
      inner ℂ (blochField (physicalMomentum q) u x) (blochField (physicalMomentum r) v x)) =
      (h^3)⁻¹ • ∑' a : Alias × Alias, inner ℂ (u a.1) (v a.2) *
        Well.rawPhysicalFourier Well.w
          (h⁻¹ • (aliasFrequency q a.1 - aliasFrequency r a.2)) := by
  have hi := integral_tsum_of_summable_integral_norm
    (weightedAliasGram_integrable hh q r u v)
    (weightedAliasGram_integral_norm_summable hh q r u v hu hv)
  have hpoint (x : Space) : (∑' a, weightedAliasGram h q r u v a x) =
      (Well.w (h • x) : ℂ) *
        inner ℂ (blochField (physicalMomentum q) u x) (blochField (physicalMomentum r) v x) := by
    change (∑' a : Alias × Alias, (Well.w (h • x) : ℂ) *
      inner ℂ (aliasWave q u x a.1) (aliasWave r v x a.2)) = _
    rw [blochField_inner_series q r u v hu hv x, tsum_mul_left]
  simp only [hpoint, weightedAliasGram_integral hh] at hi
  rw [← hi]
  simp only [Complex.real_smul, tsum_mul_left]

theorem scaled_aliasFrequency_sub {h : ℝ} (hh : 0 < h)
    (p p' : Space) (ν μ : Alias) :
    h⁻¹ • (aliasFrequency (h • p) ν - aliasFrequency (h • p') μ) =
      aliasTransfer h p p' ν μ := by
  rw [aliasFrequency_sub, smul_add, ← smul_sub, smul_smul, inv_mul_cancel₀ hh.ne', one_smul,
    smul_smul]
  unfold aliasTransfer
  rw [mul_comm h⁻¹ Real.pi, ← div_eq_mul_inv]

/-- The unitary angular Fourier normalization used in the paper. -/
def fourierNormalization : ℝ := (2 * Real.pi) ^ (-(3 / 2 : ℝ))

theorem normalized_blochField_gram {h : ℝ} (hh : 0 < h)
    (p p' : Space) (u v : FiberSpace)
    (hu : Summable (fun ν => ‖u ν‖)) (hv : Summable (fun ν => ‖v ν‖)) :
    ((h^3 * fourierNormalization^2 : ℝ) : ℂ) *
      (∫ x, (Well.w (h • x) : ℂ) *
        inner ℂ (blochField (physicalMomentum (h • p)) u x)
          (blochField (physicalMomentum (h • p')) v x)) =
      (fourierNormalization : ℂ) * ∑' a : Alias × Alias,
        inner ℂ (u a.1) (v a.2) * Well.physicalFourier Well.w (aliasTransfer h p p' a.1 a.2) := by
  rw [weighted_blochField_gram hh _ _ u v hu hv]
  simp only [scaled_aliasFrequency_sub hh, Complex.real_smul]
  have hterm (a : Alias × Alias) : inner ℂ (u a.1) (v a.2) *
      Well.physicalFourier Well.w (aliasTransfer h p p' a.1 a.2) =
      (fourierNormalization : ℂ) *
        (inner ℂ (u a.1) (v a.2) * Well.rawPhysicalFourier Well.w
          (aliasTransfer h p p' a.1 a.2)) := by
    unfold Well.physicalFourier fourierNormalization
    simp only [Complex.real_smul]
    ring
  simp only [hterm, tsum_mul_left]
  push_cast
  have hn : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  field_simp [hn]

#print axioms weighted_blochField_gram
#print axioms normalized_blochField_gram

end Maxwell.Continuum.EffectiveMass
