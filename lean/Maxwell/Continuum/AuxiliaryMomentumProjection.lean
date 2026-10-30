import Maxwell.Continuum.AuxiliaryHighMomentumFiber

/-! Literal projections onto high Bloch momentum. They act on every
polarization and reciprocal alias, and commute with the full cutoff
Maxwell inverse. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.Auxiliary

open FreeFiber FiberAnalytic PeriodicBand Bloch MeasureTheory

attribute [local irreducible] Bloch.unitary Auxiliary.resolvent cutoffFiber cutoffOperator

def highMomentumSet (s : ℝ) : Set QuasiCell := {q | s ≤ ‖q.val‖}

theorem highMomentumSet_measurable (s : ℝ) : MeasurableSet (highMomentumSet s) :=
  (isClosed_le continuous_const continuous_subtype_val.norm).measurableSet

def highMomentumFiber (s : ℝ) : QuasiCell → FiberMap :=
  (highMomentumSet s).indicator (fun _ => ContinuousLinearMap.id ℂ FiberSpace)

theorem highMomentumFiber_apply (s : ℝ) (q : QuasiCell) (u : FiberSpace) :
    highMomentumFiber s q u = if s ≤ ‖q.val‖ then u else 0 := by
  by_cases hq : s ≤ ‖q.val‖
  · rw [highMomentumFiber, Set.indicator_of_mem (show q ∈ highMomentumSet s from hq)]
    simp [hq]
  · rw [highMomentumFiber, Set.indicator_of_notMem (show q ∉ highMomentumSet s from hq)]
    simp [hq]

def highMomentumData (s : ℝ) : FiberMultiplier.Data (H := FiberSpace) quasiMeasure 1 where
  operator := highMomentumFiber s
  measurable := aestronglyMeasurable_const.indicator (highMomentumSet_measurable s)
  nonneg := by norm_num
  bound q := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    rw [highMomentumFiber_apply]
    split_ifs <;> simp

def highMomentumProjection (s : ℝ) : FieldL2 →L[ℂ] FieldL2 :=
  physicalize (highMomentumData s).multiplier

theorem highMomentumProjection_ae (s : ℝ) (f : FieldL2) :
    unitary (highMomentumProjection s f) =ᵐ[quasiMeasure]
      fun q => if s ≤ ‖q.val‖ then unitary f q else 0 := by
  rw [highMomentumProjection, unitary_physicalize]
  filter_upwards [(highMomentumData s).multiplier_ae (unitary f)] with q hq
  exact hq.trans (highMomentumFiber_apply s q _)

theorem highMomentumProjection_norm_le (s : ℝ) : ‖highMomentumProjection s‖ ≤ 1 :=
  physicalize_norm_le _ (by norm_num) (highMomentumData s).multiplier_norm_le

theorem highMomentumProjection_selfAdjoint (s : ℝ) : IsSelfAdjoint (highMomentumProjection s) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  apply physicalize_symmetric
  apply (highMomentumData s).multiplier_symmetric
  intro q u v
  change inner ℂ (highMomentumFiber s q u) v = inner ℂ u (highMomentumFiber s q v)
  rw [highMomentumFiber_apply, highMomentumFiber_apply]
  split_ifs <;> simp

theorem highMomentumProjection_nested {r s : ℝ} (hrs : r ≤ s) :
    highMomentumProjection s * highMomentumProjection r = highMomentumProjection s := by
  apply ContinuousLinearMap.ext
  intro f
  apply unitary.injective
  apply Lp.ext
  filter_upwards [highMomentumProjection_ae s (highMomentumProjection r f),
    highMomentumProjection_ae r f, highMomentumProjection_ae s f] with q hs hr hf
  change unitary (highMomentumProjection s (highMomentumProjection r f)) q = unitary (highMomentumProjection s f) q
  rw [hs, hr, hf]
  by_cases hq : s ≤ ‖q.val‖
  · simp [hq, hrs.trans hq]
  · simp [hq]

theorem highMomentumProjection_idempotent (s : ℝ) :
    highMomentumProjection s * highMomentumProjection s = highMomentumProjection s :=
  highMomentumProjection_nested le_rfl

theorem highMomentumProjection_resolvent {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (s : ℝ) :
    highMomentumProjection s * resolvent D hσ0 hσ = resolvent D hσ0 hσ * highMomentumProjection s := by
  apply ContinuousLinearMap.ext
  intro f
  apply unitary.injective
  apply Lp.ext
  filter_upwards [highMomentumProjection_ae s (resolvent D hσ0 hσ f),
    resolvent_ae D hσ0 hσ f, resolvent_ae D hσ0 hσ (highMomentumProjection s f),
    highMomentumProjection_ae s f] with q hp hr hrp hpf
  change unitary (highMomentumProjection s (resolvent D hσ0 hσ f)) q =
    unitary (resolvent D hσ0 hσ (highMomentumProjection s f)) q
  rw [hp, hr, hrp, hpf]
  split_ifs <;> simp only [map_zero]

theorem highMomentumProjection_resolvent_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) {s : ℝ} (hs : smallRadius/4 ≤ s) :
    ‖highMomentumProjection s * resolvent D hσ0 hσ‖ ≤ (2 : ℝ)^192 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [← unitary.norm_map f, ← unitary.norm_map ((highMomentumProjection s * resolvent D hσ0 hσ) f)]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [highMomentumProjection_ae s (resolvent D hσ0 hσ f), resolvent_ae D hσ0 hσ f]
    with q hp hr
  change ‖unitary (highMomentumProjection s (resolvent D hσ0 hσ f)) q‖ ≤ _
  rw [hp, hr]
  split_ifs with hq
  · exact ((cutoffFiber z σ q).le_of_opNorm_le
      (highMomentum_cutoffFiber_norm_le D hσ0 hσ q (hs.trans hq)) _).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
  · rw [norm_zero]
    positivity

#print axioms highMomentumProjection_resolvent
#print axioms highMomentumProjection_resolvent_norm_le

end Maxwell.Continuum.Auxiliary
