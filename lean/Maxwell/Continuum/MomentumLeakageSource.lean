import Maxwell.Continuum.MomentumLeakageIteration
import Maxwell.Continuum.EffectiveMassActualSource
import Maxwell.Continuum.BlochTranslationFiber

/-! The nested-cutoff estimate for the actual normalized auxiliary
source, and exact translation covariance of high-momentum projections. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open MeasureTheory Bloch PeriodicBand EffectiveMass

attribute [local irreducible] Bloch.unitary highMomentumProjection Auxiliary.resolvent actualSource muH realMode Wh

theorem highMomentumProjection_translation (s : ℝ) (a : Space) (f : FieldL2) :
    highMomentumProjection s (fieldTranslation a f) =
      fieldTranslation a (highMomentumProjection s f) := by
  apply unitary.injective
  apply Lp.ext
  filter_upwards [highMomentumProjection_ae s (fieldTranslation a f),
    unitary_fieldTranslation_ae a f, unitary_fieldTranslation_ae a (highMomentumProjection s f),
    highMomentumProjection_ae s f] with q hp ht htp hf
  rw [hp, ht, htp, hf]
  split_ifs <;> simp only [map_zero]

theorem highMomentumProjection_translation_norm (s : ℝ) (a : Space) (f : FieldL2) :
    ‖highMomentumProjection s (fieldTranslation a f)‖ = ‖highMomentumProjection s f‖ := by
  rw [highMomentumProjection_translation, (fieldTranslation a).norm_map]

theorem translatedWell_zero (h : ℝ) : translatedWell h (0 : Space) = Wh h := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [translatedWell_ae h 0 f j, Wh_ae h f j] with x ht hw
  rw [ht, hw, sub_zero]

theorem finiteWell_single (h v : ℝ) :
    finiteWellOperator h (fun _ : Unit => (0 : Space)) (fun _ => v) = (v : ℂ) • Wh h := by
  classical
  simp only [finiteWellOperator, Finset.univ_unique, Finset.sum_singleton, translatedWell_zero]

theorem source_inverse_eigenvalue_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) : (muH D hh)⁻¹ ≤ (2 : ℝ)^128*h^2 := by
  have hlo := (muH_bounds D hh).1
  have hp : 0 < (1/(2 : ℝ)^128)*(h^2)⁻¹ :=
    mul_pos (by positivity) (inv_pos.mpr (sq_pos_of_pos D.h_pos))
  have hi := (inv_le_inv₀ (muH_pos D hh) hp).mpr hlo
  simpa only [mul_inv_rev, inv_inv, one_div, mul_comm] using hi

theorem actualSource_nested_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (Δ : ℝ) (hΔ : 0 ≤ Δ) (K : ℕ) :
    ‖highMomentumProjection (smallRadius/4+(K : ℝ)*Δ) (actualSource D hh)‖ ≤
      (1/4 : ℝ)^K + (2 : ℝ)^233*Real.exp (-Real.sqrt (Δ/h)/512) := by
  have hv0 : 0 ≤ (muH D hh)⁻¹ := (inv_pos.mpr (muH_pos D hh)).le
  have hv : (muH D hh)⁻¹ ≤ (2 : ℝ)^130*h^2 :=
    (source_inverse_eigenvalue_bound D hh).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg h))
  have heq : actualSource D hh = (0 : FieldL2) +
      finiteWellOperator h (fun _ : Unit => (0 : Space)) (fun _ => (muH D hh)⁻¹)
        (resolvent D le_rfl (by positivity) (actualSource D hh)) := by
    rw [zero_add, finiteWell_single]
    change actualSource D hh = (((muH D hh)⁻¹ : ℝ) : ℂ) •
      Wh h (resolvent D le_rfl (by positivity) (actualSource D hh))
    rw [Complex.ofReal_inv]
    exact actualSource_equation D hh
  have hb := finiteWell_nested_bound D le_rfl (by positivity) hh
    (fun _ : Unit => (0 : Space)) (fun _ => (muH D hh)⁻¹) (fun _ => hv0) (fun _ => hv)
    (by intro i j hij; exact (hij (Subsingleton.elim i j)).elim)
    (actualSource D hh) 0 heq (smallRadius/4) Δ 0 le_rfl hΔ le_rfl
    (by intro s _; simp) K
  simp only [Fintype.card_unique, Nat.cast_one, mul_one, zero_add] at hb
  calc
    _ ≤ ((1/4 : ℝ)^K+(2 : ℝ)^233*Real.exp (-Real.sqrt (Δ/h)/512)) * ‖actualSource D hh‖ := by
      apply hb.trans_eq
      ring
    _ ≤ ((1/4 : ℝ)^K+(2 : ℝ)^233*Real.exp (-Real.sqrt (Δ/h)/512)) * 1 :=
      mul_le_mul_of_nonneg_left (actualSource_norm_le D hh) (by positivity)
    _ = _ := mul_one _

#print axioms highMomentumProjection_translation
#print axioms actualSource_nested_bound

end Maxwell.Continuum.Auxiliary
