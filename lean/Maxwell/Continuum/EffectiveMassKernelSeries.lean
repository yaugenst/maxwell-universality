import Maxwell.Continuum.EffectiveMassKernelPhase
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Absolutely summable alias-pair expansion of the actual physical
Bloch-wave Gram integrand. No alias is discarded. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open FreeFiber CellBandFourier MeasureTheory

def aliasWave (q : Space) (u : FiberSpace) (x : Space) (ν : Alias) : Polarization :=
  angularPhase (aliasFrequency q ν) x • u ν

theorem aliasWave_norm (q : Space) (u : FiberSpace) (x : Space) (ν : Alias) :
    ‖aliasWave q u x ν‖ = ‖u ν‖ := by
  rw [aliasWave, norm_smul, angularPhase_norm, one_mul]

theorem aliasWave_hasSum (q : Space) (u : FiberSpace)
    (hu : Summable (fun ν => ‖u ν‖)) (x : Space) :
    HasSum (aliasWave q u x) (blochField (physicalMomentum q) u x) := by
  have h := blochField_hasSum (physicalMomentum q) u hu x
  change HasSum (fun ν => angularPhase (aliasFrequency q ν) x • u ν) _
  simpa only [← aliasFrequency_momentum, spatialPhase_physical] using h

theorem aliasGram_summable (q r : Space) (u v : FiberSpace)
    (hu : Summable (fun ν => ‖u ν‖)) (hv : Summable (fun ν => ‖v ν‖)) (x : Space) :
    Summable (fun a : Alias × Alias => inner ℂ (aliasWave q u x a.1) (aliasWave r v x a.2)) := by
  apply Summable.of_norm_bounded (hu.mul_of_nonneg hv (fun ν => norm_nonneg _) (fun ν => norm_nonneg _))
  intro a
  simpa only [aliasWave_norm] using norm_inner_le_norm (𝕜 := ℂ)
    (aliasWave q u x a.1) (aliasWave r v x a.2)

theorem blochField_inner_series (q r : Space) (u v : FiberSpace)
    (hu : Summable (fun ν => ‖u ν‖)) (hv : Summable (fun ν => ‖v ν‖)) (x : Space) :
    inner ℂ (blochField (physicalMomentum q) u x) (blochField (physicalMomentum r) v x) =
      ∑' a : Alias × Alias, inner ℂ (aliasWave q u x a.1) (aliasWave r v x a.2) := by
  have hsum := aliasGram_summable q r u v hu hv x
  have hf := aliasWave_hasSum q u hu x
  have hg := aliasWave_hasSum r v hv x
  have hrow (ν : Alias) := (innerSL ℂ (aliasWave q u x ν)).hasSum hg
  rw [hsum.tsum_prod' (fun ν => (hrow ν).summable)]
  simp only [show ∀ ν, (∑' μ, inner ℂ (aliasWave q u x ν) (aliasWave r v x μ)) =
      inner ℂ (aliasWave q u x ν) (blochField (physicalMomentum r) v x) from
    fun ν => (hrow ν).tsum_eq]
  exact (((innerSL ℂ).flip (blochField (physicalMomentum r) v x)).hasSum hf).tsum_eq.symm

theorem aliasGram_phase (q r : Space) (u v : FiberSpace) (x : Space) (ν μ : Alias) :
    inner ℂ (aliasWave q u x ν) (aliasWave r v x μ) =
      inner ℂ (u ν) (v μ) * angularPhase (-(aliasFrequency q ν - aliasFrequency r μ)) x := by
  rw [aliasWave, aliasWave, inner_smul_left, inner_smul_right]
  change star (angularPhase (aliasFrequency q ν) x) *
    (angularPhase (aliasFrequency r μ) x * inner ℂ (u ν) (v μ)) = _
  rw [angularPhase_star, ← mul_assoc, ← angularPhase_add]
  rw [show -aliasFrequency q ν + aliasFrequency r μ =
    -(aliasFrequency q ν - aliasFrequency r μ) by abel]
  exact mul_comm _ _

def weightedAliasGram (h : ℝ) (q r : Space) (u v : FiberSpace) (a : Alias × Alias) (x : Space) : ℂ :=
  (Well.w (h • x) : ℂ) * inner ℂ (aliasWave q u x a.1) (aliasWave r v x a.2)

theorem weightedAliasGram_integrable {h : ℝ} (hh : 0 < h)
    (q r : Space) (u v : FiberSpace) (a : Alias × Alias) :
    Integrable (weightedAliasGram h q r u v a) := by
  have hi := (modulated_scaled_well_integrable hh
    (-(aliasFrequency q a.1 - aliasFrequency r a.2))).mul_const (inner ℂ (u a.1) (v a.2))
  apply hi.congr
  exact Filter.Eventually.of_forall fun x => by
    rw [weightedAliasGram, aliasGram_phase]
    ring

theorem weightedAliasGram_integral_norm_bound {h : ℝ} (hh : 0 < h)
    (q r : Space) (u v : FiberSpace) (a : Alias × Alias) :
    (∫ x, ‖weightedAliasGram h q r u v a x‖) ≤
      (∫ x : Space, Well.w (h • x)) * (‖u a.1‖ * ‖v a.2‖) := by
  rw [← integral_mul_const]
  apply integral_mono (weightedAliasGram_integrable hh q r u v a).norm
    ((scaled_well_integrable hh).mul_const _)
  intro x
  change ‖weightedAliasGram h q r u v a x‖ ≤ _
  rw [weightedAliasGram, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Well.w_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Well.w_nonneg _)
  simpa only [aliasWave_norm] using norm_inner_le_norm (𝕜 := ℂ)
    (aliasWave q u x a.1) (aliasWave r v x a.2)

theorem weightedAliasGram_integral_norm_summable {h : ℝ} (hh : 0 < h)
    (q r : Space) (u v : FiberSpace)
    (hu : Summable (fun ν => ‖u ν‖)) (hv : Summable (fun ν => ‖v ν‖)) :
    Summable (fun a : Alias × Alias => ∫ x, ‖weightedAliasGram h q r u v a x‖) := by
  apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (weightedAliasGram_integral_norm_bound hh q r u v)
  exact (hu.mul_of_nonneg hv (fun ν => norm_nonneg _) (fun ν => norm_nonneg _)).mul_left _

#print axioms blochField_inner_series
#print axioms weightedAliasGram_integral_norm_summable

end Maxwell.Continuum.EffectiveMass
