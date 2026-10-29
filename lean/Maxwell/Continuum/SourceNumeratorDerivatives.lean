import Maxwell.Continuum.SourceNumerator

/-! Uniform analytic derivatives of the actual scaled source numerator.
All estimates retain the compact source and the full normalized cell mode. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber CellBandFourier PeriodicBand FiberNormalization Set Metric

attribute [local irreducible] Auxiliary.resolvent PeriodicPerturbation.perturbation
  PeriodicPerturbation.finiteK CornerBridge.topState RankOneBand.Data.bandRoot
  scaledBand clusterVector fiberVector normalizedFiberVector physicalFiberVector

theorem sourceImaginary_add (q p : Momentum) :
    sourceImaginary (q+p) = sourceImaginary q + sourceImaginary p := by
  apply PiLp.ext
  intro j
  simp only [sourceImaginary, PiLp.toLp_apply, Pi.add_apply, Complex.add_im]
  rfl

theorem sourceImaginary_neg (q : Momentum) : sourceImaginary (-q) = -sourceImaginary q := by
  apply PiLp.ext
  intro j
  simp only [sourceImaginary, PiLp.toLp_apply, Pi.neg_apply, Complex.neg_im]
  rfl

theorem sourceImaginary_real_smul (h : ℝ) (q : Momentum) :
    sourceImaginary ((h : ℂ) • q) = h • sourceImaginary q := by
  apply PiLp.ext
  intro j
  simp only [sourceImaginary, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rfl

theorem sourceImaginary_norm_le (q : Momentum) : ‖sourceImaginary q‖ ≤ 2 * ‖q‖ := by
  have hsq : ‖sourceImaginary q‖^2 ≤ 3 * ‖q‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hb (j : Fin 3) : ‖(q j).im‖^2 ≤ ‖q‖^2 := by
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      have hj : ‖(q j).im‖ ≤ ‖q j‖ := by
        simpa only [Real.norm_eq_abs] using Complex.abs_im_le_norm (q j)
      exact hj.trans (norm_le_pi_norm q j)
    simpa only [sourceImaginary, PiLp.toLp_apply, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using
      (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hb j))
  nlinarith only [hsq, norm_nonneg (sourceImaginary q), norm_nonneg q, sq_nonneg ‖q‖]

theorem source_physicalChart_isOpen : IsOpen physicalChart := by
  change IsOpen {q : Momentum | ∀ j, ‖q j‖ < analyticRadius}
  simpa only [ofPred_forall] using
    (isOpen_iInter_of_finite (fun j : Fin 3 => isOpen_lt (continuous_apply j).norm continuous_const))

theorem source_physicalChart_neg {q : Momentum} (hq : q ∈ physicalChart) : -q ∈ physicalChart := by
  intro j
  simpa only [Pi.neg_apply, norm_neg] using hq j

def scaledSourceFactor (h : ℝ) (u : FieldL2) (k : Momentum) : ℂ :=
  (sourceScale h : ℂ) * sourceFactor h u ((h : ℂ) • k)

def scaledSourceProduct (h : ℝ) (u : FieldL2) (k : Momentum) : ℂ :=
  scaledSourceFactor h u k * scaledSourceFactor h u (-k)

theorem scaledSourceProduct_eq {h : ℝ} (hh : 0 < h) (u : FieldL2) (k : Momentum) :
    scaledSourceProduct h u k = (h^3 : ℂ) *
      sourceFactor h u ((h : ℂ) • k) * sourceFactor h u (-((h : ℂ) • k)) := by
  have hs : sourceScale h ^ 2 = h^3 := by
    rw [sourceScale, mul_pow, Real.sq_sqrt hh.le]
    ring
  unfold scaledSourceProduct scaledSourceFactor
  rw [smul_neg]
  calc
    _ = (sourceScale h : ℂ)^2 * sourceFactor h u ((h : ℂ) • k) *
        sourceFactor h u (-((h : ℂ) • k)) := by ring
    _ = _ := by rw [← Complex.ofReal_pow, hs, Complex.ofReal_pow]

theorem scaledSourceFactor_norm_le {h : ℝ} (hh : 0 < h) (u : FieldL2)
    {k : Momentum} (hk : (h : ℂ) • k ∈ physicalChart) :
    ‖scaledSourceFactor h u k‖ ≤ 96 * Real.exp ‖sourceImaginary k‖ * ‖u‖ := by
  rw [scaledSourceFactor, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sourceScale_pos hh)]
  have he : ‖sourceImaginary ((h : ℂ) • k)‖ / h = ‖sourceImaginary k‖ := by
    rw [sourceImaginary_real_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hh,
      mul_div_cancel_left₀ _ hh.ne']
  simpa only [he] using sourceFactor_scaled_norm_le hh u hk

theorem scaledSourceFactor_curve_analytic {h : ℝ} (hh : 0 < h) (u : FieldL2)
    {g : ℂ → Momentum} {U : Set ℂ} (hU : IsOpen U) (hg : AnalyticOnNhd ℂ g U)
    (hmap : MapsTo (fun z => (h : ℂ) • g z) U physicalChart) :
    AnalyticOnNhd ℂ (fun z => scaledSourceFactor h u (g z)) U := by
  have hs : AnalyticOnNhd ℂ (fun z => (h : ℂ) • g z) U :=
    fun z hz => (hg z hz).const_smul (c := (h : ℂ))
  intro z hz
  exact analyticAt_const.mul (sourceFactor_curve_analytic hh u hU hs hmap z hz)

theorem scaledSourceProduct_curve_analytic {h : ℝ} (hh : 0 < h) (u : FieldL2)
    {g : ℂ → Momentum} {U : Set ℂ} (hU : IsOpen U) (hg : AnalyticOnNhd ℂ g U)
    (hmap : MapsTo (fun z => (h : ℂ) • g z) U physicalChart) :
    AnalyticOnNhd ℂ (fun z => scaledSourceProduct h u (g z)) U := by
  intro z hz
  apply (scaledSourceFactor_curve_analytic hh u hU hg hmap z hz).mul
  apply scaledSourceFactor_curve_analytic hh u hU (fun z hz => (hg z hz).neg) _ z hz
  intro w hw
  simpa only [Pi.neg_apply, smul_neg] using source_physicalChart_neg (hmap hw)

theorem scaledSourceProduct_norm_le {h : ℝ} (hh : 0 < h) (u : FieldL2)
    {k : Momentum} (hk : (h : ℂ) • k ∈ physicalChart) :
    ‖scaledSourceProduct h u k‖ ≤ (96 * Real.exp ‖sourceImaginary k‖ * ‖u‖)^2 := by
  rw [scaledSourceProduct, norm_mul, pow_two]
  apply mul_le_mul (scaledSourceFactor_norm_le hh u hk) _ (norm_nonneg _) (by positivity)
  have hneg : (h : ℂ) • (-k) ∈ physicalChart := by
    simpa only [smul_neg] using source_physicalChart_neg hk
  simpa only [sourceImaginary_neg, norm_neg] using scaledSourceFactor_norm_le hh u hneg

theorem scaledSourceProduct_norm_ledger {h : ℝ} (hh : 0 < h) {u : FieldL2} (hu : ‖u‖ ≤ 1)
    {k : Momentum} (hk : (h : ℂ) • k ∈ physicalChart) (hi : ‖sourceImaginary k‖ ≤ 16) :
    ‖scaledSourceProduct h u k‖ ≤ (2 : ℝ)^64 := by
  have he : Real.exp (16 : ℝ) ≤ (3 : ℝ)^16 := by
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 16
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using hp
  have hb : 96 * Real.exp ‖sourceImaginary k‖ * ‖u‖ ≤ (2 : ℝ)^32 := by
    calc
      _ ≤ 96 * ((3 : ℝ)^16) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr hi).trans he) (by norm_num))
          hu (norm_nonneg _) (by positivity)
      _ ≤ _ := by norm_num
  apply (scaledSourceProduct_norm_le hh u hk).trans
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 96 * Real.exp ‖sourceImaginary k‖ * ‖u‖) hb 2
  simpa only [← pow_mul] using hp

theorem scaledSourceProduct_line_analytic {h : ℝ} (hh : 0 < h) (u : FieldL2) (k v : Momentum) :
    AnalyticOnNhd ℂ (fun z : ℂ => scaledSourceProduct h u (k + z • v))
      {z : ℂ | (h : ℂ) • (k + z • v) ∈ physicalChart} := by
  have hc : Continuous (fun z : ℂ => (h : ℂ) • (k + z • v)) := by fun_prop
  apply scaledSourceProduct_curve_analytic hh u
    (source_physicalChart_isOpen.preimage hc)
    (fun _ _ => analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  intro z hz
  exact hz

/-- Every fixed derivative order is bounded uniformly in h. The hypotheses
are explicit chart margins and physical imaginary-momentum bounds only. -/
theorem scaledSourceProduct_iteratedDeriv_le {h : ℝ} (hh : 0 < h) (hhR : h ≤ analyticRadius)
    {u : FieldL2} (hu : ‖u‖ ≤ 1) {k v : Momentum}
    (hk : ‖(h : ℂ) • k‖ ≤ analyticRadius / 2) (hi : ‖sourceImaginary k‖ ≤ 8)
    (hv : ‖v‖ ≤ 1) (n : ℕ) :
    ‖iteratedDeriv n (fun z : ℂ => scaledSourceProduct h u (k + z • v)) 0‖ ≤
      n.factorial * (2 : ℝ)^(4*n+64) := by
  have hchart : ∀ z ∈ closedBall (0 : ℂ) (1/16),
      (h : ℂ) • (k + z • v) ∈ physicalChart := by
    intro z hz j
    have hz' : ‖z‖ ≤ 1/16 := by simpa only [mem_closedBall, dist_zero_right] using hz
    have hd : ‖(h : ℂ) • (z • v)‖ ≤ h / 16 := by
      rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
      have hb := mul_le_mul hz' hv (norm_nonneg _) (by norm_num)
      nlinarith only [hb, hh]
    apply (norm_le_pi_norm ((h : ℂ) • (k + z • v)) j).trans_lt
    rw [smul_add]
    exact (norm_add_le _ _).trans_lt (by linarith only [hk, hd, hhR, analyticRadius_pos])
  have him : ∀ z ∈ closedBall (0 : ℂ) (1/16), ‖sourceImaginary (k + z • v)‖ ≤ 16 := by
    intro z hz
    have hz' : ‖z‖ ≤ 1/16 := by simpa only [mem_closedBall, dist_zero_right] using hz
    rw [sourceImaginary_add]
    apply (norm_add_le _ _).trans
    have hd := sourceImaginary_norm_le (z • v)
    rw [norm_smul] at hd
    have hb := mul_le_mul hz' hv (norm_nonneg _) (by norm_num)
    linarith only [hi, hd, hb]
  have ha := (scaledSourceProduct_line_analytic hh u k v).mono hchart
  have hb := CauchyBounds.norm_iteratedDeriv_le n ha
    (fun z hz => scaledSourceProduct_norm_ledger hh hu (hchart z hz) (him z hz))
    (r := 1/16) (c := 0) (by norm_num) (by norm_num)
  apply hb.trans_eq
  rw [div_eq_mul_inv, ← inv_pow]
  rw [show (1/16 : ℝ)⁻¹ = 16 by norm_num,
    show (16 : ℝ) = 2^4 by norm_num, ← pow_mul, mul_assoc, ← pow_add]
  congr 2
  omega

#print axioms scaledSourceProduct_eq
#print axioms scaledSourceProduct_curve_analytic
#print axioms scaledSourceProduct_iteratedDeriv_le

end Maxwell.Continuum.EffectiveMass
