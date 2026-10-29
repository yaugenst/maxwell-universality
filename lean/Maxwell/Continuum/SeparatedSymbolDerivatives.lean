import Maxwell.Continuum.SeparatedSymbolAnalytic
import Maxwell.Continuum.OperatorGevrey
import Maxwell.Continuum.AuxiliaryCutoff

/-! Actual directional derivative estimates for the complete separated
continuum symbol on the support of the physical cutoff. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber FiberAnalytic PeriodicBand OperatorFourier Set Metric

local instance : NormedSpace ℝ FiberMap := NormedSpace.complexToReal

attribute [local irreducible] separatedSymbol

def realMomentumMap : Space →L[ℝ] Momentum :=
  ContinuousLinearMap.pi (fun j => Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j))

theorem realMomentumMap_apply (q : Space) :
    realMomentumMap q = realMomentum (fun j => q j) := rfl

theorem realMomentumMap_norm_le (q : Space) : ‖realMomentumMap q‖ ≤ ‖q‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).mpr
  intro j
  change ‖(q j : ℂ)‖ ≤ ‖q‖
  simpa only [Complex.norm_real] using PiLp.norm_apply_le q j

theorem separated_line_mem {q v : Momentum} (hq : ‖q‖ ≤ separatedRadius / 2)
    (hv : ‖v‖ ≤ 1) {s : ℂ} (hs : s ∈ closedBall 0 (separatedRadius / 2)) :
    q + s • v ∈ closedBall 0 separatedRadius := by
  rw [mem_closedBall, dist_zero_right]
  have hs' : ‖s‖ ≤ separatedRadius / 2 := by simpa using hs
  have htri := norm_add_le q (s • v)
  rw [norm_smul] at htri
  nlinarith [norm_nonneg s]

theorem separated_line_analytic {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    {q v : Momentum} (hq : ‖q‖ ≤ separatedRadius / 2) (hv : ‖v‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun s : ℂ => separatedSymbol z σ (q + s • v))
      (closedBall 0 (separatedRadius / 2)) := by
  intro s hs
  exact AnalyticAt.comp (f := fun s : ℂ => q + s • v)
    (separatedSymbol_analytic D hσ0 hσ _ (separated_line_mem hq hv hs))
    (analyticAt_const.add (analyticAt_id.smul analyticAt_const))

theorem separated_line_derivative_bound {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    {q v : Momentum} (hq : ‖q‖ ≤ separatedRadius / 2) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    ‖iteratedDeriv K (fun s : ℝ => separatedSymbol z σ (q + (s : ℂ) • v)) 0‖ ≤
      (2 : ℝ)^112 * ((2 : ℝ)^156)^K * (K.factorial : ℝ)^2 := by
  let f : ℂ → FiberMap := fun s => separatedSymbol z σ (q + s • v)
  have ha : AnalyticOnNhd ℂ f (closedBall 0 (separatedRadius / 2)) :=
    separated_line_analytic D hσ0 hσ hq hv
  have hc : ∀ s ∈ closedBall (0 : ℂ) (separatedRadius / 2), ‖f s‖ ≤ (2 : ℝ)^112 := by
    intro s hs
    exact separatedSymbol_norm_le D hσ0 hσ
      (by simpa using separated_line_mem hq hv hs)
  change ‖iteratedDeriv K (fun s : ℝ => f s) 0‖ ≤ _
  erw [OperatorFourier.iteratedDeriv_restrict_complex f (ball 0 (separatedRadius / 2))
    isOpen_ball (ha.mono ball_subset_closedBall) K 0 (by simpa using
      (half_pos separatedRadius_pos))]
  have hd := CauchyBounds.norm_iteratedDeriv_le K ha hc
    (half_pos separatedRadius_pos) (c := 0) (by simp)
  have hr : (separatedRadius / 2)⁻¹ ≤ (2 : ℝ)^156 := by
    norm_num [separatedRadius, backgroundAmplitude]
  have hfac : (K.factorial : ℝ) ≤ (K.factorial : ℝ)^2 := by
    have hpos : (1 : ℝ) ≤ K.factorial := by exact_mod_cast Nat.factorial_pos K
    nlinarith
  have hr0 : 0 ≤ (separatedRadius / 2)⁻¹ := (inv_pos.mpr (half_pos separatedRadius_pos)).le
  calc
    ‖iteratedDeriv K f 0‖ ≤ K.factorial * (2 : ℝ)^112 / (separatedRadius / 2)^K := hd
    _ = (2 : ℝ)^112 * ((separatedRadius / 2)⁻¹)^K * K.factorial := by
      rw [div_eq_mul_inv, ← inv_pow]
      ring
    _ ≤ (2 : ℝ)^112 * ((2 : ℝ)^156)^K * (K.factorial : ℝ)^2 := by
      gcongr

def realSeparatedSymbol (z σ : ℝ) (q : Space) : FiberMap := separatedSymbol z σ (realMomentumMap q)

theorem realSeparatedSymbol_contDiffAt {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    {q : Space} (hq : ‖q‖ ≤ separatedRadius) :
    ContDiffAt ℝ (⊤ : ℕ∞) (realSeparatedSymbol z σ) q := by
  have hm : realMomentumMap q ∈ closedBall 0 separatedRadius := by
    simpa using (realMomentumMap_norm_le q).trans hq
  exact ((separatedSymbol_analytic D hσ0 hσ _ hm).contDiffAt.restrict_scalars ℝ).comp q
    realMomentumMap.contDiff.contDiffAt

theorem realSeparatedSymbol_line_bound {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    {q v : Space} (hq : ‖q‖ ≤ separatedRadius / 2) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    ‖iteratedDeriv K (fun s : ℝ => realSeparatedSymbol z σ (q + s • v)) 0‖ ≤
      (2 : ℝ)^112 * ((2 : ℝ)^156)^K * (K.factorial : ℝ)^2 := by
  have he : (fun s : ℝ => realSeparatedSymbol z σ (q + s • v)) =
      (fun s : ℝ => separatedSymbol z σ (realMomentumMap q + (s : ℂ) • realMomentumMap v)) := by
    funext s
    rw [realSeparatedSymbol, map_add, map_smul]
    rfl
  rw [he]
  exact separated_line_derivative_bound D hσ0 hσ ((realMomentumMap_norm_le q).trans hq)
    ((realMomentumMap_norm_le v).trans hv) K

#print axioms separated_line_derivative_bound
#print axioms realSeparatedSymbol_line_bound

end Maxwell.Continuum.Auxiliary
