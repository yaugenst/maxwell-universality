import Maxwell.Continuum.PeriodicPolePlane
import Maxwell.Continuum.WellCutoffDeriv

/-! Literal auxiliary cutoffs for the local pole split. These are the
paper's fixed rescalings of the already constructed convolution cutoff. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric TransverseGaussian

def poleLongitudinalScale : ℝ := (2^2048 : ℝ)⁻¹
def poleTransverseScale : ℝ := (2^4100 : ℝ)⁻¹
def poleCoreRadius : ℝ := (2^4102 : ℝ)⁻¹

theorem poleCutoff_scales : 0 < poleLongitudinalScale ∧ 0 < poleTransverseScale ∧
    0 < poleCoreRadius ∧ poleCoreRadius ≤ poleTransverseScale ∧
    poleTransverseScale ≤ poleLongitudinalScale ∧
    4 * poleTransverseScale ≤ poleGaussianRadius ∧
    2 * poleLongitudinalScale ≤ longitudinalPoleRadius / 8 := by
  norm_num [poleLongitudinalScale, poleTransverseScale, poleCoreRadius,
    poleGaussianRadius, longitudinalPoleRadius]

def scaledPsi (a u : ℝ) : ℝ := Well.psi (u / a)

theorem scaledPsi_contDiff (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (scaledPsi a) :=
  Well.psi_contDiff.comp (contDiff_id.div_const a)

theorem scaledPsi_nonneg (a u : ℝ) : 0 ≤ scaledPsi a u := Well.psi_nonneg _
theorem scaledPsi_le_one (a u : ℝ) : scaledPsi a u ≤ 1 := Well.psi_le_one _

theorem scaledPsi_eq_one {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : |u| ≤ a) : scaledPsi a u = 1 := by
  apply Well.psi_eq_one
  rw [abs_div, abs_of_pos ha]
  exact (div_le_one ha).mpr hu

theorem scaledPsi_eq_zero {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : 2 * a ≤ |u|) : scaledPsi a u = 0 := by
  apply Well.psi_eq_zero_of_two_le
  rw [abs_div, abs_of_pos ha]
  exact (le_div_iff₀ ha).mpr hu

theorem scaledPsi_support {a : ℝ} (ha : 0 < a) : Function.support (scaledPsi a) ⊆ Icc (-2*a) (2*a) := by
  intro u hu
  have hn : |u| < 2 * a := by
    by_contra h
    exact hu (scaledPsi_eq_zero ha (le_of_not_gt h))
  exact ⟨by linarith only [(abs_lt.mp hn).1], (abs_lt.mp hn).2.le⟩

theorem scaledPsi_hasCompactSupport {a : ℝ} (ha : 0 < a) : HasCompactSupport (scaledPsi a) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (scaledPsi_support ha)

theorem scaledPsi_derivative_bound {a : ℝ} (ha : 0 < a) (n : ℕ) (u : ℝ) :
    |iteratedDeriv n (scaledPsi a) u| ≤ 16 * (800 / a)^n * (n.factorial : ℝ)^2 := by
  have he : scaledPsi a = fun x => Well.psi (a⁻¹ * x) := by
    funext x
    simp only [scaledPsi, div_eq_mul_inv, mul_comm]
  rw [he, iteratedDeriv_comp_const_mul (Well.psi_contDiff.of_le (by simp)), abs_mul,
    abs_pow, abs_inv, abs_of_pos ha]
  have hb := mul_le_mul_of_nonneg_left (Well.psi_gevrey n (a⁻¹ * u))
    (pow_nonneg (inv_nonneg.mpr ha.le) n)
  exact hb.trans_eq (by rw [div_pow, div_eq_mul_inv, inv_pow]; ring)

def poleLongitudinalCutoff : ℝ → ℝ := scaledPsi poleLongitudinalScale
def poleTransverseCutoff (x : Plane) : ℝ := ∏ k : Fin 2, scaledPsi poleTransverseScale (x k)
def poleChartCutoff (j : Fin 3) (q : Space) : ℝ :=
  poleLongitudinalCutoff (q j) * ∏ k : Fin 2, scaledPsi poleTransverseScale (q (j.succAbove k))

theorem poleChartCutoff_nonneg (j : Fin 3) (q : Space) : 0 ≤ poleChartCutoff j q := by
  exact mul_nonneg (scaledPsi_nonneg _ _) (Finset.prod_nonneg (fun _ _ => scaledPsi_nonneg _ _))

theorem poleChartCutoff_le_one (j : Fin 3) (q : Space) : poleChartCutoff j q ≤ 1 := by
  unfold poleChartCutoff poleLongitudinalCutoff
  have hp := Finset.prod_le_one₀ (s := Finset.univ)
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin 2))) => scaledPsi_nonneg poleTransverseScale (q (j.succAbove k)))
    (fun k _ => scaledPsi_le_one poleTransverseScale (q (j.succAbove k)))
  simpa only [one_mul] using mul_le_mul (scaledPsi_le_one poleLongitudinalScale (q j)) hp
    (Finset.prod_nonneg (fun _ _ => scaledPsi_nonneg _ _)) (by norm_num : (0 : ℝ) ≤ 1)

theorem poleChartCutoff_contDiff (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (poleChartCutoff j) := by
  apply ContDiff.mul
  · exact (scaledPsi_contDiff poleLongitudinalScale).comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Space →L[ℝ] ℝ).contDiff
  · apply contDiff_prod
    intro k _
    exact (scaledPsi_contDiff poleTransverseScale).comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (j.succAbove k) : Space →L[ℝ] ℝ).contDiff

theorem poleChartCutoff_core (j : Fin 3) {q : Space} (hq : ‖q‖ ≤ poleCoreRadius) :
    poleChartCutoff j q = 1 := by
  have hcoord (k : Fin 3) : |q k| ≤ poleCoreRadius := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le q k).trans hq
  unfold poleChartCutoff poleLongitudinalCutoff
  rw [scaledPsi_eq_one poleCutoff_scales.1
    ((hcoord j).trans (poleCutoff_scales.2.2.2.1.trans poleCutoff_scales.2.2.2.2.1)), one_mul]
  exact Finset.prod_eq_one fun k _ => scaledPsi_eq_one poleCutoff_scales.2.1
    ((hcoord _).trans poleCutoff_scales.2.2.2.1)

theorem poleTransverseCutoff_nonneg (x : Plane) : 0 ≤ poleTransverseCutoff x :=
  Finset.prod_nonneg (fun _ _ => scaledPsi_nonneg _ _)

theorem poleTransverseCutoff_le_one (x : Plane) : poleTransverseCutoff x ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => scaledPsi_nonneg _ _) (fun _ _ => scaledPsi_le_one _ _)

theorem poleTransverseCutoff_core {x : Plane} (hx : ‖x‖ ≤ poleTransverseScale) :
    poleTransverseCutoff x = 1 := by
  apply Finset.prod_eq_one
  intro k _
  apply scaledPsi_eq_one poleCutoff_scales.2.1
  simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x k).trans hx

theorem poleTransverseCutoff_support {x : Plane} (hx : poleTransverseCutoff x ≠ 0) :
    ‖x‖ ≤ 4 * poleTransverseScale := by
  have hr := poleCutoff_scales.2.1
  have hcoord (k : Fin 2) : |x k| ≤ 2 * poleTransverseScale := by
    have hk : scaledPsi poleTransverseScale (x k) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hx) k (Finset.mem_univ _)
    have hm := scaledPsi_support poleCutoff_scales.2.1 hk
    exact abs_le.mpr ⟨by linarith only [hm.1], hm.2⟩
  have hs : ‖x‖^2 ≤ 2 * (2 * poleTransverseScale)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have h0 := (sq_le_sq₀ (abs_nonneg (x 0)) (by positivity : 0 ≤ 2*poleTransverseScale)).mpr (hcoord 0)
    have h1 := (sq_le_sq₀ (abs_nonneg (x 1)) (by positivity : 0 ≤ 2*poleTransverseScale)).mpr (hcoord 1)
    rw [sq_abs] at h0 h1
    linarith only [h0, h1]
  nlinarith only [hs, norm_nonneg x, hr]

#print axioms poleChartCutoff_core
#print axioms scaledPsi_derivative_bound

end Maxwell.Continuum.PeriodicBand
