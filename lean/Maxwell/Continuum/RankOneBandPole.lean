import Maxwell.Continuum.RankOneBandPoleFactors
import Maxwell.Continuum.RankOneBandProjection

/-! Exact simple-pole decomposition of the literal inverse. The residue
has rank one, while the explicitly separated inverse is analytic through
the band root. No Riesz projection is assumed. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand.Data

set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped NNReal Topology ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ} (D : Data K u ell)
variable {V : E → ℂ → H →L[ℂ] H} {U : Set E} (P : PerturbationData V U ell)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem resolvent_pole_factor (p : E) (hp : p ∈ U) (e : ℂ) :
    resolvent K u ell (V p e) e = (e - D.bandRoot P p)⁻¹ • D.poleNumerator P p e -
      highSolve K u ell (V p e) e := by
  unfold resolvent poleNumerator
  rw [← D.scalarResidual_factor P p hp e, mul_inv, smul_smul]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem resolvent_pole_formula (p : E) (hp : p ∈ U) (e : ℂ) (hne : e ≠ D.bandRoot P p) :
    resolvent K u ell (V p e) e =
      (e - D.bandRoot P p)⁻¹ • D.poleResidue P p + D.separatedResolvent P p e := by
  rw [D.resolvent_pole_factor P p hp e]
  unfold separatedResolvent
  rw [dslope_of_ne _ hne]
  change (e - D.bandRoot P p)⁻¹ • D.poleNumerator P p e - highSolve K u ell (V p e) e =
    (e - D.bandRoot P p)⁻¹ • D.poleNumerator P p (D.bandRoot P p) +
      ((e - D.bandRoot P p)⁻¹ •
        (D.poleNumerator P p e - D.poleNumerator P p (D.bandRoot P p)) - highSolve K u ell (V p e) e)
  rw [smul_sub]
  abel

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem scaled_resolvent_pole_formula (p : E) (hp : p ∈ U) (e : ℂ) (hne : e ≠ D.bandRoot P p) :
    (e - D.bandRoot P p) • resolvent K u ell (V p e) e =
      D.poleResidue P p + (e - D.bandRoot P p) • D.separatedResolvent P p e := by
  rw [D.resolvent_pole_formula P p hp e hne, smul_add, smul_smul,
    mul_inv_cancel₀ (sub_ne_zero.mpr hne), one_smul]

variable (hV : AnalyticOnNhd ℂ (Function.uncurry V) (U ×ˢ closedBall (ell : ℂ) (1 / 100)))
include hV

theorem poleResidue_range (p : E) (hp : p ∈ U) :
    (D.poleResidue P p).range = (operator K (V p (D.bandRoot P p)) (D.bandRoot P p)).ker := by
  have hm := D.bandRoot_mem P p hp
  rw [poleResidue, poleNumerator, D.scaledRankOne_range _ _ _
    (inv_ne_zero (D.poleDivisor_ne_zero P hV p hp _ hm)),
    D.kernel_eq_span _ _ (P.small p hp _ hm) (by simpa only [mem_closedBall, dist_eq_norm] using hm)
      (D.bandRoot_fixed P p hp)]

theorem poleResidue_finrank (p : E) (hp : p ∈ U) : Module.finrank ℂ (D.poleResidue P p).range = 1 := by
  rw [D.poleResidue_range P hV p hp]
  exact D.bandRoot_kernel_finrank P p hp

theorem poleResidue_ne_zero (p : E) (hp : p ∈ U) : D.poleResidue P p ≠ 0 := by
  intro hz
  have h := D.poleResidue_finrank P hV p hp
  rw [hz] at h
  change Module.finrank ℂ (LinearMap.range (0 : H →ₗ[ℂ] H)) = 1 at h
  rw [LinearMap.range_zero] at h
  simp at h

omit hV [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem poleResidue_projection (p : E) (hp : p ∈ U) :
    D.poleResidue P p =
      (numerator K u ell (V p (D.bandRoot P p)) (D.bandRoot P p)
        (eigenvectorLift K u ell (V p (D.bandRoot P p)) (D.bandRoot P p)) /
        deriv (fun z => scalarResidual K u ell (V p z) z) (D.bandRoot P p)) •
      normalizedProjection K u ell (V p (D.bandRoot P p)) (D.bandRoot P p) := by
  have hm := D.bandRoot_mem P p hp
  have hn := D.numerator_lift_ne_zero _ _ (P.small p hp _ hm)
    (by simpa only [mem_closedBall, dist_eq_norm] using hm)
  unfold poleResidue poleNumerator poleDivisor normalizedProjection
  rw [dslope_same, smul_smul, div_eq_mul_inv]
  congr 1
  rw [mul_comm (numerator _ _ _ _ _ _), mul_assoc, mul_inv_cancel₀ hn, mul_one]

theorem tendsto_scaled_resolvent (p : E) (hp : p ∈ U) :
    Tendsto (fun e => (e - D.bandRoot P p) • resolvent K u ell (V p e) e)
      (𝓝[≠] D.bandRoot P p) (𝓝 (D.poleResidue P p)) := by
  have hs := (D.analyticAt_separatedResolvent P hV p hp _ (D.bandRoot_mem P p hp)).continuousAt
  have ht : Tendsto (fun e => D.poleResidue P p + (e - D.bandRoot P p) • D.separatedResolvent P p e)
      (𝓝 (D.bandRoot P p)) (𝓝 (D.poleResidue P p)) := by
    have hid : Tendsto (fun e : ℂ => e - D.bandRoot P p)
        (𝓝 (D.bandRoot P p)) (𝓝 (0 : ℂ)) := by
      have hi : Tendsto (fun e : ℂ => e) (𝓝 (D.bandRoot P p)) (𝓝 (D.bandRoot P p)) := tendsto_id
      simpa only [sub_self] using hi.sub_const (D.bandRoot P p)
    have hc : Tendsto (fun _ : ℂ => D.poleResidue P p)
        (𝓝 (D.bandRoot P p)) (𝓝 (D.poleResidue P p)) := tendsto_const_nhds
    simpa only [zero_smul, add_zero] using hc.add (hid.smul hs)
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  exact (D.scaled_resolvent_pole_formula P p hp e he).symm

#print axioms resolvent_pole_formula
#print axioms poleResidue_finrank
#print axioms poleResidue_projection
#print axioms tendsto_scaled_resolvent

end Maxwell.Continuum.RankOneBand.Data
