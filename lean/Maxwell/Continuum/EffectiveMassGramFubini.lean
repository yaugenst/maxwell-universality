import Maxwell.Continuum.EffectiveMassPacketIntegral

/-! A dominated Fubini identity for the well-weighted Gram form of
bounded packet waves. This is an integral theorem, with no operator
identity among its hypotheses. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory

variable {X P : Type*} [MeasurableSpace X] [MeasurableSpace P]
  {μ : Measure X} {ν : Measure P} [SFinite μ] [SFinite ν]

theorem bounded_wave_gram (a : X × P → ℂ) (ha : StronglyMeasurable a)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x p, ‖a (x,p)‖ ≤ C)
    (w : X → ℂ) (hw : Integrable w μ) (hwm : StronglyMeasurable w)
    (f g : P → ℂ) (hf : Integrable f ν) (hg : Integrable g ν)
    (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g) :
    (∫ x, w x * star (∫ p, f p * a (x,p) ∂ν) * (∫ r, g r * a (x,r) ∂ν) ∂μ) =
      ∫ p, star (f p) * (∫ r, g r * (∫ x, w x * star (a (x,p)) * a (x,r) ∂μ) ∂ν) ∂ν := by
  let H : X × (P × P) → ℂ := fun xp =>
    w xp.1 * star (f xp.2.1 * a (xp.1,xp.2.1)) * (g xp.2.2 * a (xp.1,xp.2.2))
  have hH : StronglyMeasurable H := by
    unfold H
    exact ((hwm.comp_measurable measurable_fst).mul
      (((hfm.comp_measurable measurable_snd.fst).mul
        (ha.comp_measurable (measurable_fst.prodMk measurable_snd.fst))).star)).mul
      ((hgm.comp_measurable measurable_snd.snd).mul
        (ha.comp_measurable (measurable_fst.prodMk measurable_snd.snd)))
  have hi : Integrable H (μ.prod (ν.prod ν)) := by
    apply ((hw.norm.mul_const (C*C)).mul_prod (hf.norm.mul_prod hg.norm)).mono'
      hH.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun xp => by
      change ‖H xp‖ ≤ (‖w xp.1‖ * (C*C)) * (‖f xp.2.1‖ * ‖g xp.2.2‖)
      simp only [H, norm_mul, norm_star]
      calc
        _ = (‖w xp.1‖ * ‖f xp.2.1‖ * ‖g xp.2.2‖) *
          (‖a (xp.1,xp.2.1)‖ * ‖a (xp.1,xp.2.2)‖) := by ring
        _ ≤ (‖w xp.1‖ * ‖f xp.2.1‖ * ‖g xp.2.2‖) * (C*C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hbound _ _) (hbound _ _) (norm_nonneg _) hC)
            (by positivity)
        _ = _ := by ring
  calc
    _ = ∫ x, ∫ pr : P × P, H (x,pr) ∂ν.prod ν ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [show (∫ pr : P × P, H (x,pr) ∂ν.prod ν) =
          w x * ∫ pr : P × P, star (f pr.1 * a (x,pr.1)) * (g pr.2 * a (x,pr.2)) ∂ν.prod ν by
            rw [← integral_const_mul]; apply integral_congr_ae
            exact Filter.Eventually.of_forall fun _ => by dsimp only [H]; ring]
        rw [integral_prod_mul (fun p => star (f p * a (x,p))) (fun r => g r * a (x,r))]
        have hs : (∫ p, star (f p * a (x,p)) ∂ν) = star (∫ p, f p * a (x,p) ∂ν) := integral_conj
        rw [hs]
        ring
    _ = ∫ pr : P × P, ∫ x, H (x,pr) ∂μ ∂ν.prod ν := integral_integral_swap hi
    _ = ∫ p, ∫ r, ∫ x, H (x,(p,r)) ∂μ ∂ν ∂ν := integral_prod _ hi.integral_prod_right
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
            simp only [H, star_mul]
            ring

#print axioms bounded_wave_gram

end Maxwell.Continuum.EffectiveMass
