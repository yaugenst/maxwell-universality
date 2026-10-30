import Maxwell.Continuum.DerivativeCellSymbol
import Maxwell.Continuum.CutoffLocalSymbol
import Maxwell.Continuum.FullCellGevrey

/-! Local Cauchy estimates and all-order cutoff Gevrey bounds for the
actual derivative resolvent. The analyticity radius is proportional to h. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.CellGauge

open FreeFiber Auxiliary PeriodicBand OperatorFourier Set Metric

local instance derivativeCellGevreyRealSpace : NormedSpace ℝ CellMap := NormedSpace.complexToReal

attribute [local irreducible] derivativeCellSymbol

theorem realDerivativeCellSymbol_contDiffAt {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) {q : Space} (hq : ‖realMomentumMap q‖ ≤ 4 * smallRadius) :
    ContDiffAt ℝ (⊤ : ℕ∞) (realSymbol (derivativeCellSymbol z σ j)) q := by
  have hb : hessianEnergy (0 : Corner.Vec) ≤ (99 / 100 : ℝ)^2 * h^2 := by
    simp only [hessianEnergy_diagonal, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
      mul_zero, Finset.sum_const_zero]
    positivity
  have ha := derivativeCellSymbol_tube_analyticAt D hh hσ0 hσ j (fun k => q k) 0 hq hb
  have he : shiftedMomentum (fun k => q k) 0 = realMomentumMap q := by
    funext k
    change (q k : ℂ) + Complex.I * ((0 : ℝ) : ℂ) = (q k : ℂ)
    simp
  rw [he] at ha
  exact (ha.contDiffAt.restrict_scalars ℝ).comp q realMomentumMap.contDiff.contDiffAt

theorem derivativeCell_line_analytic {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) {q v : Space} (hq : ‖realMomentumMap q‖ ≤ 3 * smallRadius) (hv : ‖v‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun s : ℂ => derivativeCellSymbol z σ j
      (realMomentumMap q + s • realMomentumMap v)) (closedBall 0 (fullCellRadius h)) := by
  intro s hs
  have hsn : ‖s‖ ≤ fullCellRadius h := by simpa using hs
  have ha := derivativeCellSymbol_tube_analyticAt D hh hσ0 hσ j
    (fun k => q k + s.re * v k) (fun k => s.im * v k)
    (fullCell_line_real_bound D hq hv hsn) (fullCell_line_imaginary_bound hv hsn)
  rw [← fullCell_line_shift] at ha
  exact ha.comp (f := fun s : ℂ => realMomentumMap q + s • realMomentumMap v)
    (analyticAt_const.add (analyticAt_id.smul analyticAt_const))

theorem derivativeCell_line_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) {q v : Space} (hq : ‖realMomentumMap q‖ ≤ 3 * smallRadius) (hv : ‖v‖ ≤ 1)
    {s : ℂ} (hs : s ∈ closedBall 0 (fullCellRadius h)) :
    ‖derivativeCellSymbol z σ j (realMomentumMap q + s • realMomentumMap v)‖ ≤
      (2 : ℝ)^32 * (h^4)⁻¹ := by
  have hsn : ‖s‖ ≤ fullCellRadius h := by simpa using hs
  rw [fullCell_line_shift]
  exact derivativeCellSymbol_tube_norm_le D hh hσ0 hσ j
    (fun k => q k + s.re * v k) (fun k => s.im * v k)
    (fullCell_line_real_bound D hq hv hsn) (fullCell_line_imaginary_bound hv hsn)

theorem derivativeCell_line_derivative_bound {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) {q v : Space} (hq : ‖realMomentumMap q‖ ≤ 3 * smallRadius) (hv : ‖v‖ ≤ 1)
    (K : ℕ) :
    ‖iteratedDeriv K (fun s : ℝ => realSymbol (derivativeCellSymbol z σ j) (q + s • v)) 0‖ ≤
      ((2 : ℝ)^32 * (h^4)⁻¹) * ((2 : ℝ)^256 / h)^K * (K.factorial : ℝ)^2 := by
  have hpos := D.h_pos
  let f : ℂ → CellMap := fun s => derivativeCellSymbol z σ j
    (realMomentumMap q + s • realMomentumMap v)
  have ha : AnalyticOnNhd ℂ f (closedBall 0 (fullCellRadius h)) :=
    derivativeCell_line_analytic D hh hσ0 hσ j hq hv
  have hc : ∀ s ∈ closedBall (0 : ℂ) (fullCellRadius h),
      ‖f s‖ ≤ (2 : ℝ)^32 * (h^4)⁻¹ := by
    intro s hs
    exact derivativeCell_line_norm_le D hh hσ0 hσ j hq hv hs
  have he : (fun s : ℝ => realSymbol (derivativeCellSymbol z σ j) (q + s • v)) =
      (fun s : ℝ => f s) := by
    funext s
    rw [realSymbol, map_add, map_smul]
    rfl
  rw [he, OperatorFourier.iteratedDeriv_restrict_complex f (ball 0 (fullCellRadius h))
    isOpen_ball (ha.mono ball_subset_closedBall) K 0
    (by simpa using fullCellRadius_pos D.h_pos)]
  have hd := CauchyBounds.norm_iteratedDeriv_le K ha hc
    (fullCellRadius_pos D.h_pos) (c := 0) (by simp)
  have hfac : (K.factorial : ℝ) ≤ (K.factorial : ℝ)^2 := by
    have hp : (1 : ℝ) ≤ K.factorial := by exact_mod_cast Nat.factorial_pos K
    nlinarith
  calc
    _ ≤ K.factorial * ((2 : ℝ)^32 * (h^4)⁻¹) / (fullCellRadius h)^K := hd
    _ = ((2 : ℝ)^32 * (h^4)⁻¹) * ((2 : ℝ)^256 / h)^K * K.factorial := by
      have hr : (fullCellRadius h)⁻¹ = (2 : ℝ)^256 / h := by
        rw [fullCellRadius, inv_div]
      have hrK : ((fullCellRadius h)^K)⁻¹ = ((2 : ℝ)^256 / h)^K := by
        rw [← inv_pow]
        exact congrArg (fun r : ℝ => r^K) hr
      rw [div_eq_mul_inv, hrK]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfac (by positivity)

theorem cutoffDerivativeCellSymbol_contDiff {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffDerivativeCellSymbol z σ j) :=
  cutoffSymbol_local_contDiff _ fun _ hq =>
    realDerivativeCellSymbol_contDiffAt D hh hσ0 hσ j (hq.trans (by linarith [smallRadius_pos]))

theorem cutoffDerivativeCellSymbol_gevrey {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (q v : Space) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    ‖directionalDerivative K (cutoffDerivativeCellSymbol z σ j) q v‖ ≤
      ((2 : ℝ)^77 * (h^4)⁻¹) * ((2 : ℝ)^257 / h)^K * (K.factorial : ℝ)^2 := by
  have hb := cutoffSymbol_local_gevrey (derivativeCellSymbol z σ j)
    (fun _ hq => realDerivativeCellSymbol_contDiffAt D hh hσ0 hσ j
      (hq.trans (by linarith [smallRadius_pos]))) (C := (2 : ℝ)^32 * (h^4)⁻¹)
    (by positivity) (fullCell_gevrey_rate D)
    (fun _ _ hq hv K => derivativeCell_line_derivative_bound D hh hσ0 hσ j hq hv K) q v hv K
  have hc : (2 : ℝ)^45 * ((2 : ℝ)^32 * (h^4)⁻¹) = (2 : ℝ)^77 * (h^4)⁻¹ := by ring
  have hr : 2 * ((2 : ℝ)^256 / h) = (2 : ℝ)^257 / h := by ring
  rw [hc, hr] at hb
  exact hb

theorem cutoffDerivativeCellSymbol_fourier_decay {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (p : Space) :
    ‖angularFourier (cutoffDerivativeCellSymbol z σ j) p‖ ≤
      24 * ((2 : ℝ)^77 * (h^4)⁻¹) *
        Real.exp (-Real.sqrt (400 * ‖p‖ / ((2 : ℝ)^257 / h)) / 64) := by
  have hpos := D.h_pos
  apply angularFourier_gevrey_decay (cutoffDerivativeCellSymbol z σ j)
    (cutoffDerivativeCellSymbol_contDiff D hh hσ0 hσ j)
    (cutoffSymbol_compact (derivativeCellSymbol z σ j))
    ((cutoffSymbol_tsupport (derivativeCellSymbol z σ j)).trans
      (closedBall_subset_closedBall (by norm_num [smallRadius, backgroundAmplitude])))
    (by positivity) (by positivity)
  intro K q v hv
  exact cutoffDerivativeCellSymbol_gevrey D hh hσ0 hσ j q v hv K

#print axioms cutoffDerivativeCellSymbol_gevrey
#print axioms cutoffDerivativeCellSymbol_fourier_decay

end Maxwell.Continuum.CellGauge
