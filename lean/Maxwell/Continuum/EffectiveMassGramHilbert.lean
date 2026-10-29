import Maxwell.Continuum.EffectiveMassGramFubini

/-! The well-weighted packet Gram identity for vector-valued waves. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory

variable {X P H : Type*} [MeasurableSpace X] [MeasurableSpace P]
  {μ : Measure X} {ν : Measure P} [SFinite μ] [SFinite ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integral_inner_product (f g : P → H) (hf : Integrable f ν) (hg : Integrable g ν) :
    (∫ pr : P × P, inner ℂ (f pr.1) (g pr.2) ∂ν.prod ν) =
      inner ℂ (∫ p, f p ∂ν) (∫ r, g r ∂ν) := by
  have hi : Integrable (fun pr : P × P => inner ℂ (f pr.1) (g pr.2)) (ν.prod ν) :=
    hf.op_fst_snd continuous_inner ⟨1, by simpa only [one_mul] using norm_inner_le_norm (𝕜 := ℂ)⟩ hg
  rw [integral_prod _ hi]
  simp only [integral_inner hg]
  exact ((innerSL ℂ).flip (∫ r, g r ∂ν)).integral_comp_commSL RCLike.conj_smul hf

theorem bounded_hilbert_wave_gram (a : X × P → H) (ha : StronglyMeasurable a)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x p, ‖a (x,p)‖ ≤ C)
    (w : X → ℂ) (hw : Integrable w μ) (hwm : StronglyMeasurable w)
    (f g : P → ℂ) (hf : Integrable f ν) (hg : Integrable g ν)
    (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g) :
    (∫ x, w x * inner ℂ (∫ p, f p • a (x,p) ∂ν) (∫ r, g r • a (x,r) ∂ν) ∂μ) =
      ∫ p, star (f p) * (∫ r, g r * (∫ x, w x * inner ℂ (a (x,p)) (a (x,r)) ∂μ) ∂ν) ∂ν := by
  have hrow (b : P → ℂ) (hb : Integrable b ν) (hbm : StronglyMeasurable b) (x : X) :
      Integrable (fun p => b p • a (x,p)) ν := by
    apply (hb.norm.mul_const C).mono'
      (hbm.smul (ha.comp_measurable measurable_prodMk_left)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      change ‖b p • a (x,p)‖ ≤ ‖b p‖ * C
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hbound x p) (norm_nonneg _)
  let T : X × (P × P) → ℂ := fun xp =>
    w xp.1 * inner ℂ (f xp.2.1 • a (xp.1,xp.2.1)) (g xp.2.2 • a (xp.1,xp.2.2))
  have hT : StronglyMeasurable T := by
    unfold T
    exact (hwm.comp_measurable measurable_fst).mul
      (((hfm.comp_measurable measurable_snd.fst).smul
        (ha.comp_measurable (measurable_fst.prodMk measurable_snd.fst))).inner
      ((hgm.comp_measurable measurable_snd.snd).smul
        (ha.comp_measurable (measurable_fst.prodMk measurable_snd.snd))))
  have hi : Integrable T (μ.prod (ν.prod ν)) := by
    apply ((hw.norm.mul_const (C*C)).mul_prod (hf.norm.mul_prod hg.norm)).mono'
      hT.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun xp => by
      change ‖T xp‖ ≤ (‖w xp.1‖ * (C*C)) * (‖f xp.2.1‖ * ‖g xp.2.2‖)
      dsimp only [T]
      rw [norm_mul]
      calc
        _ ≤ ‖w xp.1‖ * (‖f xp.2.1 • a (xp.1,xp.2.1)‖ *
          ‖g xp.2.2 • a (xp.1,xp.2.2)‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
        _ = (‖w xp.1‖ * ‖f xp.2.1‖ * ‖g xp.2.2‖) *
          (‖a (xp.1,xp.2.1)‖ * ‖a (xp.1,xp.2.2)‖) := by simp only [norm_smul]; ring
        _ ≤ (‖w xp.1‖ * ‖f xp.2.1‖ * ‖g xp.2.2‖) * (C*C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hbound _ _) (hbound _ _) (norm_nonneg _) hC)
            (by positivity)
        _ = _ := by ring
  calc
    _ = ∫ x, ∫ pr : P × P, T (x,pr) ∂ν.prod ν ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [show (∫ pr : P × P, T (x,pr) ∂ν.prod ν) =
          w x * ∫ pr : P × P, inner ℂ (f pr.1 • a (x,pr.1)) (g pr.2 • a (x,pr.2)) ∂ν.prod ν by
            rw [← integral_const_mul]]
        rw [integral_inner_product _ _ (hrow f hf hfm x) (hrow g hg hgm x)]
    _ = ∫ pr : P × P, ∫ x, T (x,pr) ∂μ ∂ν.prod ν := integral_integral_swap hi
    _ = ∫ p, ∫ r, ∫ x, T (x,(p,r)) ∂μ ∂ν ∂ν := integral_prod _ hi.integral_prod_right
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun r => by
          dsimp only
          rw [← integral_const_mul, ← integral_const_mul]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            simp only [T, inner_smul_left, inner_smul_right, starRingEnd_apply]
            ring

#print axioms bounded_hilbert_wave_gram

end Maxwell.Continuum.EffectiveMass
