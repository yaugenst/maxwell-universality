import Maxwell.Continuum.PoleTailJets
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Uniform integrable bounds for all positive-order tail derivatives.
The constants do not depend on the height of the pole above the axis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.OscillatoryPole

open Complex Real MeasureTheory Set Filter PeriodicBand
open scoped Topology ContDiff

def tailTermBound (a : ℝ) (n k : ℕ) : ℝ :=
  if k = 0 then (n.factorial : ℝ) * (2/a)^(n-1) * (8/a^2)
  else (n.choose k : ℝ) * (80 * (800/a)^k * (k.factorial : ℝ)^2) *
    ((n-k).factorial : ℝ) * (2/a)^(n-k+1)

def tailDerivativeBound (a : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), tailTermBound a n k

theorem tailTermBound_nonneg {a : ℝ} (ha : 0 < a) (n k : ℕ) :
    0 ≤ tailTermBound a n k := by
  unfold tailTermBound
  split <;> positivity

theorem tailDerivativeBound_nonneg {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 ≤ tailDerivativeBound a n :=
  Finset.sum_nonneg (fun _ _ => tailTermBound_nonneg ha _ _)

theorem pole_distance_lower {a : ℝ} (_ha : 0 < a) {p : ℂ} (hp : ‖p‖ ≤ a/2)
    {u : ℝ} (hu : a ≤ |u|) : |u|/2 ≤ ‖(u : ℂ)-p‖ ∧ a/2 ≤ ‖(u : ℂ)-p‖ := by
  have hd := norm_sub_norm_le (u : ℂ) p
  rw [Complex.norm_real, Real.norm_eq_abs] at hd
  constructor <;> linarith only [hd, hp, hu]

theorem poleJet_weighted {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {p : ℂ}
    (hp : ‖p‖ ≤ a/2) {u : ℝ} (hu : a ≤ |u|) {n : ℕ} (hn : 1 ≤ n) :
    ‖poleJet p n u‖ * (1+u^2) ≤ (n.factorial : ℝ)*(2/a)^(n-1)*(8/a^2) := by
  obtain ⟨hdu, hda⟩ := pole_distance_lower ha hp hu
  have hd : 0 < ‖(u : ℂ)-p‖ := lt_of_lt_of_le (by positivity) hda
  have hia : ‖(u : ℂ)-p‖⁻¹ ≤ 2/a := by
    simpa only [inv_div] using (inv_le_inv₀ hd (by positivity : 0 < a/2)).mpr hda
  have hasq : a^2 ≤ 1 := by nlinarith only [ha, ha1]
  have hau : a^2 ≤ u^2 := by
    have := (sq_le_sq₀ ha.le (abs_nonneg u)).mpr hu
    simpa only [sq_abs] using this
  have hud : u^2 ≤ 4*‖(u : ℂ)-p‖^2 := by
    have := (sq_le_sq₀ (by positivity : 0 ≤ |u|/2) hd.le).mpr hdu
    rw [div_pow, sq_abs] at this
    nlinarith only [this]
  have hw : (1+u^2)/‖(u : ℂ)-p‖^2 ≤ 8/a^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) (sq_pos_of_pos ha)).mpr
    have hm := mul_le_mul_of_nonneg_right hasq (sq_nonneg u)
    nlinarith only [hau, hud, hm]
  rw [poleJet_norm]
  calc
    _ = (n.factorial : ℝ)*(‖(u : ℂ)-p‖⁻¹)^(n-1)*
        ((1+u^2)/‖(u : ℂ)-p‖^2) := by
      rw [show n+1 = (n-1)+2 by omega, pow_add, inv_pow]
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hia _) (by positivity)) hw
      (by positivity) (by positivity)

theorem cutoffComplement_norm (a u : ℝ) : ‖cutoffComplement a u‖ ≤ 1 := by
  have hn := scaledPsi_nonneg a u
  have hu := scaledPsi_le_one a u
  have he : cutoffComplement a u = ((1-scaledPsi a u : ℝ) : ℂ) := by
    simp [cutoffComplement, complexCutoff]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hu)]
  linarith only [hn]

theorem cutoffComplement_derivative_bound {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hk : 0 < k) (u : ℝ) :
    ‖iteratedDeriv k (cutoffComplement a) u‖ ≤16*(800/a)^k*(k.factorial : ℝ)^2 := by
  rw [cutoffComplement_iteratedDeriv_pos a hk, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  exact scaledPsi_derivative_bound ha k u

theorem cutoffComplement_derivative_outside {a : ℝ} (ha : 0 < a) {k : ℕ}
    (hk : 0 < k) {u : ℝ} (hu : 2*a < |u|) :
    iteratedDeriv k (cutoffComplement a) u = 0 := by
  have he : cutoffComplement a =ᶠ[𝓝 u] fun _ => (1 : ℂ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hu] with v hv
    simp only [cutoffComplement, complexCutoff, scaledPsi_eq_zero ha hv.le,
      Complex.ofReal_zero, sub_zero]
  rw [he.iteratedDeriv_eq k, iteratedDeriv_const]
  simp only [hk.ne', ite_false]

theorem poleTail_term_weighted {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {p : ℂ} (hp : ‖p‖ ≤ a/2) {u : ℝ} (hu : a ≤ |u|) {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) :
    ‖(n.choose k : ℂ)*iteratedDeriv k (cutoffComplement a) u*poleJet p (n-k) u‖ *
      (1+u^2) ≤ tailTermBound a n k := by
  by_cases hk : k = 0
  · subst k
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero,
      Nat.sub_zero, tailTermBound, ite_true, norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg _) (cutoffComplement_norm a u))
      (by positivity)).trans (poleJet_weighted ha ha1 hp hu hn)
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    by_cases hlarge : 2*a < |u|
    · rw [cutoffComplement_derivative_outside ha hkpos hlarge, mul_zero, zero_mul,
        norm_zero, zero_mul]
      exact tailTermBound_nonneg ha n k
    · have hsmall : |u| ≤ 2*a := le_of_not_gt hlarge
      have hw : 1+u^2 ≤ 5 := by
        have hu2 : |u| ≤ 2 := hsmall.trans (by linarith only [ha1])
        have hs := (sq_le_sq₀ (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 2)).mpr hu2
        rw [sq_abs] at hs
        linarith only [hs]
      have hd := (pole_distance_lower ha hp hu).2
      have hdpos : 0 < ‖(u : ℂ)-p‖ := lt_of_lt_of_le (by positivity) hd
      have hi : ‖(u : ℂ)-p‖⁻¹ ≤ 2/a := by
        simpa only [inv_div] using (inv_le_inv₀ hdpos (by positivity : 0 < a/2)).mpr hd
      have hj : ‖poleJet p (n-k) u‖ ≤ ((n-k).factorial : ℝ)*(2/a)^(n-k+1) := by
        rw [poleJet_norm, div_eq_mul_inv, ← inv_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hi _) (by positivity)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        _ ≤ (n.choose k : ℝ)*(16*(800/a)^k*(k.factorial : ℝ)^2)*
            (((n-k).factorial : ℝ)*(2/a)^(n-k+1))*5 := by
          gcongr
          exact cutoffComplement_derivative_bound ha hkpos u
        _ = tailTermBound a n k := by simp only [tailTermBound, hk, ite_false]; ring

theorem poleTail_derivative_weighted {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {p : ℂ} (hpim : 0 < p.im) (hp : ‖p‖ ≤ a/2) {n : ℕ} (hn : 1 ≤ n) (u : ℝ) :
    ‖iteratedDeriv n (poleTail a p) u‖ ≤ tailDerivativeBound a n * (1+u^2)⁻¹ := by
  by_cases hu : |u| < a
  · rw [poleTail_iteratedDeriv_zero ha p hu, norm_zero]
    exact mul_nonneg (tailDerivativeBound_nonneg ha n) (by positivity)
  · have hw : 0 < 1+u^2 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hw, poleTail_iteratedDeriv hpim]
    calc
      _ ≤ (∑ k ∈ Finset.range (n+1),
          ‖(n.choose k : ℂ)*iteratedDeriv k (cutoffComplement a) u*poleJet p (n-k) u‖)*
          (1+u^2) := mul_le_mul_of_nonneg_right (norm_sum_le _ _) hw.le
      _ = ∑ k ∈ Finset.range (n+1),
          ‖(n.choose k : ℂ)*iteratedDeriv k (cutoffComplement a) u*poleJet p (n-k) u‖*
          (1+u^2) := Finset.sum_mul ..
      _ ≤ _ := Finset.sum_le_sum (fun k _ => poleTail_term_weighted ha ha1 hp
        (le_of_not_gt hu) hn k)

theorem poleTail_derivative_integrable {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {p : ℂ} (hpim : 0 < p.im) (hp : ‖p‖ ≤ a/2) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (iteratedDeriv n (poleTail a p)) := by
  apply (integrable_inv_one_add_sq.const_mul (tailDerivativeBound a n)).mono'
    ((poleTail_contDiff a hpim).continuous_iteratedDeriv n (by simp)).aestronglyMeasurable
  exact Eventually.of_forall (poleTail_derivative_weighted ha ha1 hpim hp hn)

theorem poleTail_derivative_l1 {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {p : ℂ} (hpim : 0 < p.im) (hp : ‖p‖ ≤ a/2) {n : ℕ} (hn : 1 ≤ n) :
    (∫u : ℝ, ‖iteratedDeriv n (poleTail a p) u‖) ≤ tailDerivativeBound a n * Real.pi := by
  have hi := (poleTail_derivative_integrable ha ha1 hpim hp hn).norm
  calc
    _ ≤ ∫u : ℝ, tailDerivativeBound a n * (1+u^2)⁻¹ :=
      integral_mono hi (integrable_inv_one_add_sq.const_mul _)
        (poleTail_derivative_weighted ha ha1 hpim hp hn)
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

#print axioms poleTail_derivative_l1

end Maxwell.Continuum.OscillatoryPole
