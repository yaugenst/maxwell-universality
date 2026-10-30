import Maxwell.Continuum.WellCutoffFrechet
import Maxwell.Continuum.IteratedFrechetEvaluation
import Maxwell.Continuum.AlmostAnalyticMixedMajorant
import Mathlib.Analysis.Complex.OperatorNorm

/-! Every mixed spatial derivative of the actual finite cutoff
extension obeys a bound independent of the truncation order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.AlmostAnalytic

open Complex PeriodicBand

theorem cutoffDerivative_frechet_le (m j : ℕ) (β q : Space) :
    ‖iteratedFDeriv ℝ m (cutoffDerivative j β) q‖ ≤
      ‖β‖^j*((2 : ℝ)^12*((2 : ℝ)^152)^(m+j)*((m+j).factorial : ℝ)^2) := by
  have he := norm_iteratedFDeriv_evaluation (Well.chi smallRadius) (Well.chi_contDiff smallRadius)
    m j q (fun _ => β)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hb := Well.chi_frechet_gevrey smallRadius smallRadius_pos (m+j) q
  have hscale : (2 : ℝ)^12/smallRadius=(2 : ℝ)^152 := by
    norm_num [smallRadius, FreeFiber.backgroundAmplitude]
  rwa [hscale] at hb

theorem cutoffTaylor_term_frechet_le {β : Space} (hβ : β ≠ 0) (m j : ℕ)
    (hj : j ≤ cutoffOrder β) (q : Space) {s : ℝ} (hs : |s| ≤ 1) :
    ‖iteratedFDeriv ℝ m (fun x => coefficient j s * (cutoffDerivative j β x : ℂ)) q‖ ≤
      ((2 : ℝ)^12*((2 : ℝ)^154)^m*(m.factorial : ℝ)^2)*(1/2 : ℝ)^j := by
  have hd := cutoffDerivative_contDiff j β
  let A : ℝ →L[ℝ] ℂ := (coefficient j s) • Complex.ofRealCLM
  have ha : ‖A‖ = ‖coefficient j s‖ := by
    dsimp only [A]
    rw [norm_smul, Complex.ofRealCLM_norm, mul_one]
  have he := A.norm_iteratedFDeriv_comp_left (hd.contDiffAt (x := q)) (n := m) (by simp)
  have he' : ‖iteratedFDeriv ℝ m (fun x => coefficient j s*(cutoffDerivative j β x : ℂ)) q‖ ≤
      ‖coefficient j s‖*‖iteratedFDeriv ℝ m (cutoffDerivative j β) q‖ := by
    have hfun : (A ∘ cutoffDerivative j β) =
        (fun x => coefficient j s*(cutoffDerivative j β x : ℂ)) := rfl
    rwa [hfun, ha] at he
  have hc : ‖coefficient j s‖ ≤ 1/(j.factorial : ℝ) := by
    rw [coefficient_norm]
    exact div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg s) hs) (by positivity)
  have hj' : j ≤ truncationOrder ((2 : ℝ)^156*‖β‖) := by
    simpa only [cutoffOrder, cutoff_scale] using hj
  calc
    _ ≤ ‖coefficient j s‖*‖iteratedFDeriv ℝ m (cutoffDerivative j β) q‖ := he'
    _ ≤ (1/(j.factorial : ℝ))*(‖β‖^j*
        ((2 : ℝ)^12*((2 : ℝ)^152)^(m+j)*((m+j).factorial : ℝ)^2)) :=
      mul_le_mul hc (cutoffDerivative_frechet_le m j β q) (norm_nonneg _) (by positivity)
    _ = (1/(j.factorial : ℝ))*‖β‖^j*
        ((2 : ℝ)^12*((2 : ℝ)^152)^(m+j)*((m+j).factorial : ℝ)^2) := by ring
    _ ≤ _ := mixed_factorial_majorant (norm_pos_iff.mpr hβ) m j hj'

theorem cutoffTaylor_frechet_le {β : Space} (hβ : β ≠ 0) (m : ℕ) (q : Space)
    {s : ℝ} (hs : |s| ≤ 1) :
    ‖iteratedFDeriv ℝ m (fun x => cutoffTaylor (cutoffOrder β) smallRadius x β s) q‖ ≤
      (2 : ℝ)^13*((2 : ℝ)^154)^m*(m.factorial : ℝ)^2 := by
  have he : (fun x => cutoffTaylor (cutoffOrder β) smallRadius x β s) =
      (fun x => ∑ j ∈ Finset.range (cutoffOrder β+1), coefficient j s*(cutoffDerivative j β x : ℂ)) := rfl
  rw [he, iteratedFDeriv_fun_sum_apply]
  · calc
      _ ≤ ∑ j ∈ Finset.range (cutoffOrder β+1),
          ‖iteratedFDeriv ℝ m (fun x => coefficient j s*(cutoffDerivative j β x : ℂ)) q‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (cutoffOrder β+1),
          ((2 : ℝ)^12*((2 : ℝ)^154)^m*(m.factorial : ℝ)^2)*(1/2 : ℝ)^j := by
        apply Finset.sum_le_sum
        intro j hj
        exact cutoffTaylor_term_frechet_le hβ m j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) q hs
      _ = ((2 : ℝ)^12*((2 : ℝ)^154)^m*(m.factorial : ℝ)^2)*
          ∑ j ∈ Finset.range (cutoffOrder β+1), (1/2 : ℝ)^j := (Finset.mul_sum _ _ _).symm
      _ ≤ ((2 : ℝ)^12*((2 : ℝ)^154)^m*(m.factorial : ℝ)^2)*2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
      _ = _ := by ring
  · intro j _
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (cutoffDerivative_contDiff j β))).contDiffAt.of_le
      (by simp)

#print axioms cutoffTaylor_frechet_le

end Maxwell.Continuum.AlmostAnalytic
