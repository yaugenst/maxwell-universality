import Maxwell.Composition.BlockModes
import Maxwell.Composition.Residual
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

/-!
# Calibrated source and readout budgets

The operators below evaluate the actual stored local mode on every disjoint
block. The paper's mode-accuracy tolerances imply whole-vector source and
readout errors, with no defect-count multiplier. Scalar cell/source rounding
is a separate explicit error contribution.
-/

noncomputable section

namespace Maxwell.Composition

variable {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype ι] [Fintype κ]

/-- One finite-stencil application to the calibrated local-mode injection. -/
def modeSource (α : ℝ) (K : E →L[ℝ] E)
    (Qt : EuclideanSpace ℝ (ι × κ) →L[ℝ] E)
    (Winv : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ))
    (q : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) : E :=
  α • K (Qt (Winv (blockInjection q g)))

/-- The complete source calibration error is controlled by one local mode
error in the Euclidean norm. -/
theorem modeSource_calibration_bound (α : ℝ) (K : E →L[ℝ] E)
    (Qt : EuclideanSpace ℝ (ι × κ) →L[ℝ] E)
    (Winv : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ))
    (qhat q : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    ‖modeSource α K Qt Winv qhat g - modeSource α K Qt Winv q g‖ ≤
      |α| * ‖K‖ * ‖Qt‖ * ‖Winv‖ * ‖qhat - q‖ * ‖g‖ := by
  have hI : blockInjection qhat g - blockInjection q g = blockInjection (qhat - q) g := by
    exact congrArg (fun T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (ι × κ) => T g)
      (blockInjection_sub qhat q)
  have hcomp : ‖K.comp (Qt.comp Winv)‖ ≤ ‖K‖ * ‖Qt‖ * ‖Winv‖ := by
    calc
      _ ≤ ‖K‖ * ‖Qt.comp Winv‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖K‖ * (‖Qt‖ * ‖Winv‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ = _ := by ring
  unfold modeSource
  rw [← smul_sub, ← map_sub, ← map_sub, ← map_sub, hI,
    norm_smul, Real.norm_eq_abs]
  calc
    _ = |α| * ‖(K.comp (Qt.comp Winv)) (blockInjection (qhat - q) g)‖ := rfl
    _ ≤ |α| * (‖K.comp (Qt.comp Winv)‖ * ‖blockInjection (qhat - q) g‖) :=
      mul_le_mul_of_nonneg_left ((K.comp (Qt.comp Winv)).le_opNorm _) (abs_nonneg _)
    _ ≤ |α| * ((‖K‖ * ‖Qt‖ * ‖Winv‖) * (‖qhat - q‖ * ‖g‖)) := by
      rw [blockInjection_norm_apply]
      gcongr
    _ = _ := by ring

/-- The stated local source-calibration tolerance implies the whole source
error budget before final source-vector rounding. -/
theorem modeSource_calibration_budget (α ε G J L wmin : ℝ)
    (K : E →L[ℝ] E) (Qt : EuclideanSpace ℝ (ι × κ) →L[ℝ] E)
    (Winv : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ))
    (qhat q : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι)
    (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (hJ : 0 < J) (hL : 0 < L) (hwmin : 0 < wmin)
    (hK : ‖K‖ ≤ J) (hQt : ‖Qt‖ ≤ 1) (hWinv : ‖Winv‖ ≤ 1 / wmin)
    (hg : ‖g‖ ≤ G) (hmode : ‖qhat - q‖ ≤ wmin * ε / (32768 * J * L)) :
    ‖modeSource α K Qt Winv qhat g - modeSource α K Qt Winv q g‖ ≤
      α * ε * G / (32768 * L) := by
  calc
    _ ≤ |α| * ‖K‖ * ‖Qt‖ * ‖Winv‖ * ‖qhat - q‖ * ‖g‖ :=
      modeSource_calibration_bound α K Qt Winv qhat q g
    _ ≤ α * J * 1 * (1 / wmin) * (wmin * ε / (32768 * J * L)) * G := by
      rw [abs_of_nonneg hα]
      gcongr
    _ = α * ε * G / (32768 * L) := by field_simp

/-- Adding a separately certified final rounding error gives the emitted
source budget. Both errors concern the full source vector. -/
theorem modeSource_emitted_budget (α ε G J L wmin : ℝ)
    (K : E →L[ℝ] E) (Qt : EuclideanSpace ℝ (ι × κ) →L[ℝ] E)
    (Winv : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ))
    (qhat q : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) (fhat : E)
    (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (hJ : 0 < J) (hL : 0 < L) (hwmin : 0 < wmin)
    (hK : ‖K‖ ≤ J) (hQt : ‖Qt‖ ≤ 1) (hWinv : ‖Winv‖ ≤ 1 / wmin)
    (hg : ‖g‖ ≤ G) (hmode : ‖qhat - q‖ ≤ wmin * ε / (32768 * J * L))
    (hround : ‖fhat - modeSource α K Qt Winv qhat g‖ ≤ α * ε * G / (32768 * L)) :
    ‖fhat - modeSource α K Qt Winv q g‖ ≤ α * ε * G / (16384 * L) := by
  have hcal := modeSource_calibration_budget α ε G J L wmin K Qt Winv qhat q g
    hα hε hJ hL hwmin hK hQt hWinv hg hmode
  calc
    _ = ‖(fhat - modeSource α K Qt Winv qhat g) +
        (modeSource α K Qt Winv qhat g - modeSource α K Qt Winv q g)‖ := by
      congr 1; abel
    _ ≤ ‖fhat - modeSource α K Qt Winv qhat g‖ +
        ‖modeSource α K Qt Winv qhat g - modeSource α K Qt Winv q g‖ := norm_add_le _ _
    _ ≤ α * ε * G / (32768 * L) + α * ε * G / (32768 * L) := add_le_add hround hcal
    _ = α * ε * G / (16384 * L) := by ring

omit [NormedSpace ℝ E] in
/-- The reserved emitted-source budget is at most the manuscript's larger
`1/8192` allowance. -/
theorem emitted_source_budget_weaken (α ε G L : ℝ) (fhat fstar : E)
    (hα : 0 ≤ α) (hε : 0 ≤ ε) (hG : 0 ≤ G) (hL : 0 < L)
    (herror : ‖fhat - fstar‖ ≤ α * ε * G / (16384 * L)) :
    ‖fhat - fstar‖ ≤ α * ε * G / (8192 * L) := by
  apply herror.trans
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  linarith

/-- The actual calibrated local dot-product readout satisfies the paper's
whole-vector error allowance under the physical field amplitude bound. -/
theorem modeReadout_calibration_budget (qhat q : EuclideanSpace ℝ κ) (v : ι → ℝ)
    (y : EuclideanSpace ℝ (ι × κ)) (vmax α J cW QA ε G : ℝ)
    (hvmax : 0 < vmax) (hα : 0 < α) (hJ : 0 < J) (hcW : 0 < cW) (hQA : 0 < QA)
    (hG : 0 ≤ G) (hv : ∀ i, |v i| ≤ vmax)
    (hmode : ‖qhat - q‖ ≤ ε / (1024 * vmax * α * J * cW * QA))
    (hy : ‖y‖ ≤ 3 * α * J * cW * QA * G) :
    ‖blockReadout qhat v y - blockReadout q v y‖ ≤ 3 * ε * G / 1024 := by
  have hcal := blockReadout_calibration qhat q v vmax hvmax.le hv
  calc
    _ = ‖(blockReadout qhat v - blockReadout q v) y‖ := rfl
    _ ≤ ‖blockReadout qhat v - blockReadout q v‖ * ‖y‖ :=
      (blockReadout qhat v - blockReadout q v).le_opNorm y
    _ ≤ (vmax * ‖qhat - q‖) * (3 * α * J * cW * QA * G) := by gcongr
    _ ≤ (vmax * (ε / (1024 * vmax * α * J * cW * QA))) *
        (3 * α * J * cW * QA * G) := by gcongr
    _ = 3 * ε * G / 1024 := by field_simp

end Maxwell.Composition
