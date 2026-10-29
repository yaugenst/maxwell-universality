import Maxwell.Continuum.AnalyticFixedPointBasic

/-! Uniform convergence of the actual fixed-point iterates, and continuous
parameter dependence derived from the contraction residual estimate. -/

noncomputable section
namespace Maxwell.Continuum.AnalyticFixedPoint.Data

open Set Metric Filter
open scoped Topology NNReal

variable {E : Type*} {F G : E → ℂ → ℂ} {U : Set E} {c : ℂ} {r : ℝ} {k : ℝ≥0}
variable (D : AnalyticFixedPoint.Data F U c r k)

theorem iterate_tendstoUniformlyOn : TendstoUniformlyOn D.iterate D.point atTop U := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hk : (k : ℝ) < 1 := D.constant_lt_one
  have hlim : Tendsto (fun n : ℕ => (k : ℝ) ^ n * r) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one k.coe_nonneg hk).mul_const r
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn p hp
  have h := (D.iterate_error n p hp).trans_lt hn
  simpa only [dist_comm] using h

theorem point_dist_point_le (D' : AnalyticFixedPoint.Data G U c r k)
    (p : E) (hp : p ∈ U) {δ : ℝ}
    (hFG : ∀ z ∈ closedBall c r, dist (F p z) (G p z) ≤ δ) :
    dist (D.point p) (D'.point p) ≤ δ / (1 - (k : ℝ)) :=
  D.perturbation_bound p hp (D'.point_mem p hp) (D'.point_fixed p hp)
    (hFG _ (D'.point_mem p hp))

variable [TopologicalSpace E]

theorem continuousAt_point (p : E) (hp : p ∈ U) (hU : U ∈ 𝓝 p)
    (hF : ContinuousAt (fun q => F q (D.point p)) p) : ContinuousAt D.point p := by
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hk : (k : ℝ) < 1 := D.constant_lt_one
  have hkpos : 0 < 1 - (k : ℝ) := sub_pos.mpr hk
  have hnear := Metric.continuousAt_iff'.mp hF (ε * (1 - (k : ℝ))) (mul_pos hε hkpos)
  filter_upwards [hU, hnear] with q hq hqF
  calc
    dist (D.point q) (D.point p) = dist (D.point p) (D.point q) := dist_comm _ _
    _ ≤ dist (D.point p) (F q (D.point p)) / (1 - (k : ℝ)) :=
      D.residual_bound q hq (D.point_mem p hp)
    _ = dist (F q (D.point p)) (F p (D.point p)) / (1 - (k : ℝ)) := by
      rw [D.point_fixed p hp, dist_comm]
    _ < ε := (div_lt_iff₀ hkpos).mpr hqF

#print axioms iterate_tendstoUniformlyOn
#print axioms continuousAt_point

end Maxwell.Continuum.AnalyticFixedPoint.Data
