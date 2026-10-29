import Maxwell.Continuum.FreeFiber
import Maxwell.Continuum.RankOneBandFamilyAnalytic
import Mathlib.Topology.Algebra.Module.Star

/-! The complex bilinear pairing for analytic normalization of Fourier
eigenvectors. Conjugation is the actual coordinatewise star on the Hilbert sum. -/

noncomputable section
namespace Maxwell.Continuum.FiberNormalization

set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [StarAddMonoid H] [NormedStarGroup H] [StarModule ℂ H]

def bilinear : H →L[ℂ] H →L[ℂ] ℂ :=
  (innerSL ℂ).comp (starL ℂ : H ≃L⋆[ℂ] H).toContinuousLinearMap

@[simp] theorem bilinear_apply (v w : H) : bilinear v w = inner ℂ (star v) w := rfl

theorem bilinear_norm_le (v w : H) : ‖bilinear v w‖ ≤ ‖v‖ * ‖w‖ := by
  simpa only [bilinear_apply, norm_star] using norm_inner_le_norm (𝕜 := ℂ) (star v) w

theorem bilinear_self_real (v : H) (hv : star v = v) :
    bilinear v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [bilinear_apply, hv, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem bilinear_unit (c : H) (hc : star c = c) (hn : ‖c‖ = 1) : bilinear c c = 1 := by
  rw [bilinear_self_real c hc, hn]
  norm_num

theorem bilinear_near_unit (c v : H) (hc : star c = c) (hn : ‖c‖ = 1)
    (hv : ‖v - c‖ ≤ 1 / 5) : ‖bilinear v v - 1‖ ≤ 11 / 25 := by
  have hnorm : ‖v‖ ≤ 6 / 5 := by
    have htri := norm_add_le (v - c) c
    rw [sub_add_cancel, hn] at htri
    linarith
  have heq : bilinear v v - 1 = bilinear (v - c) v + bilinear c (v - c) := by
    rw [map_sub, sub_apply, map_sub, bilinear_unit c hc hn]
    ring
  rw [heq]
  have h₁ := (bilinear_norm_le (v - c) v).trans
    (mul_le_mul hv hnorm (norm_nonneg _) (by norm_num))
  have h₂ := bilinear_norm_le c (v - c)
  rw [hn, one_mul] at h₂
  exact (norm_add_le _ _).trans (by linarith)

variable [CompleteSpace H]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_bilinear_self {v : E → H} {p : E} (hv : AnalyticAt ℂ v p) :
    AnalyticAt ℂ (fun t => bilinear (v t) (v t)) p := by
  have hb : ContDiff ℂ ω (bilinear : H →L[ℂ] H →L[ℂ] ℂ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℂ) (E := H) (F := H →L[ℂ] ℂ) bilinear
  exact ((hb.contDiffAt.comp p hv.contDiffAt).clm_apply hv.contDiffAt).analyticAt

#print axioms bilinear_near_unit
#print axioms analyticAt_bilinear_self

end Maxwell.Continuum.FiberNormalization
