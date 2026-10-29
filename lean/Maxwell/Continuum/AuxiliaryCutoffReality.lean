import Maxwell.Continuum.AuxiliaryFiberReality
import Maxwell.Continuum.AuxiliaryCutoffFiber
import Maxwell.Continuum.BlochConjugation
import Maxwell.Continuum.WellCutoffEven

/-! Reflection of the actual cutoff fiber operator. Exact cell negation
on the support avoids any convention for the cell's boundary faces. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand Bloch CellBandFourier FiberNormalization

attribute [local irreducible] fiberResolvent fiberInverse FiberAnalytic.fullResolventExtension
  scaledBand PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK CornerBridge.topState
  RankOneBand.Data.bandRoot

theorem cutoff_neg (q : Space) : cutoff (-q) = cutoff q := Well.chi_neg _ _

theorem cutoffRegion_interior (q : QuasiCell) (hq : q ∈ cutoffRegion) :
    ∀ j, -Real.pi / 2 < q.val j := by
  have hs : 4 * smallRadius < 1 := by
    norm_num [smallRadius, backgroundAmplitude]
  intro j
  have hj := norm_le_pi_norm (quasiMomentum q) j
  change ‖(q.val j : ℂ)‖ ≤ ‖quasiMomentum q‖ at hj
  rw [Complex.norm_real, Real.norm_eq_abs] at hj
  have hb : |q.val j| < 1 := hj.trans_lt ((show ‖quasiMomentum q‖ < 4 * smallRadius from hq).trans hs)
  have hlo := (abs_lt.mp hb).1
  linarith [Real.pi_gt_three]

theorem negativeCell_quasiMomentum (q : QuasiCell)
    (hi : ∀ j, -Real.pi / 2 < q.val j) :
    quasiMomentum (negativeCell q hi) = -quasiMomentum q := by
  funext j
  simp only [quasiMomentum, negativeCell_val, PiLp.neg_apply, Pi.neg_apply, Complex.ofReal_neg]

theorem negativeCell_mem_cutoffRegion (q : QuasiCell)
    (hi : ∀ j, -Real.pi / 2 < q.val j) :
    negativeCell q hi ∈ cutoffRegion ↔ q ∈ cutoffRegion := by
  change ‖quasiMomentum (negativeCell q hi)‖ < _ ↔ ‖quasiMomentum q‖ < _
  rw [negativeCell_quasiMomentum, norm_neg]

theorem negativeFrequency_mem_cutoffRegion (qn : QuasiCell × Bloch.Alias) :
    (negativeFrequency qn).1 ∈ cutoffRegion ↔ qn.1 ∈ cutoffRegion := by
  have hf : ∀ rn : QuasiCell × Bloch.Alias, rn.1 ∈ cutoffRegion →
      (negativeFrequency rn).1 ∈ cutoffRegion := by
    rintro ⟨q,n⟩ hq
    rw [negativeFrequency_interior q (cutoffRegion_interior q hq) n]
    exact (negativeCell_mem_cutoffRegion q (cutoffRegion_interior q hq)).mpr hq
  constructor
  · intro h
    have h' := hf (negativeFrequency qn) h
    simpa only [negativeFrequency_involutive] using h'
  · exact hf qn

theorem negativeCell_involutive (q : QuasiCell)
    (hi : ∀ j, -Real.pi / 2 < q.val j)
    (hj : ∀ j, -Real.pi / 2 < (negativeCell q hi).val j) :
    negativeCell (negativeCell q hi) hj = q := by
  apply Subtype.ext
  simp only [negativeCell_val, neg_neg]

theorem cutoffFiber_negativeCell {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (q : QuasiCell) (hq : q ∈ cutoffRegion)
    (f : FiberSpace) :
    cutoffFiber z σ (negativeCell q (cutoffRegion_interior q hq)) (reversal (star f)) =
      reversal (star (cutoffFiber z σ q f)) := by
  have hqn := (negativeCell_mem_cutoffRegion q (cutoffRegion_interior q hq)).mpr hq
  rw [cutoffFiber_eq hqn, cutoffFiber_eq hq]
  change (cutoff (-q.val) : ℂ) •
      fiberResolvent z σ (-(fun j => q.val j)) (reversal (star f)) =
    reversal (star ((cutoff q.val : ℂ) • fiberResolvent z σ (fun j => q.val j) f))
  rw [cutoff_neg, fiberResolvent_reverse_star D hσ0 hσ _
    (show ‖realMomentum (fun j => q.val j)‖ ≤ 4 * smallRadius from
      (show ‖quasiMomentum q‖ < 4 * smallRadius from hq).le),
    star_smul, map_smul]
  simp only [Complex.star_def, Complex.conj_ofReal]

theorem cutoffFiber_reverse_star {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (q : QuasiCell) (hq : q ∈ cutoffRegion)
    (f : FiberSpace) :
    cutoffFiber z σ q (reversal (star f)) =
      reversal (star (cutoffFiber z σ
        (negativeCell q (cutoffRegion_interior q hq)) f)) := by
  have hqn := (negativeCell_mem_cutoffRegion q (cutoffRegion_interior q hq)).mpr hq
  have h := cutoffFiber_negativeCell D hσ0 hσ _ hqn f
  rwa [negativeCell_involutive] at h

end Maxwell.Continuum.Auxiliary
