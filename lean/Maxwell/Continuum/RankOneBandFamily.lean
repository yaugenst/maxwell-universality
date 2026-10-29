import Maxwell.Continuum.RankOneBandStability
import Maxwell.Continuum.RankOneBandKernel
import Maxwell.Continuum.RankOneBandAnalytic

/-! A constructed simple band of an actual rank-one isolated operator.
The family assumptions concern only the given perturbation's size,
energy Lipschitz constant and analyticity. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand

set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped NNReal Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {E : Type*} {K : H →L[ℂ] H} {u : H} {ell : ℝ}

def scalarMap (K : H →L[ℂ] H) (u : H) (ell : ℝ)
    (V : E → ℂ → H →L[ℂ] H) (p : E) (e : ℂ) : ℂ := rootMap K u ell (V p e) e

structure PerturbationData (V : E → ℂ → H →L[ℂ] H) (U : Set E) (ell : ℝ) : Prop where
  small : ∀ p ∈ U, ∀ e ∈ closedBall (ell : ℂ) (1 / 100), ‖V p e‖ ≤ 1 / 256
  energy_lipschitz : ∀ p ∈ U,
    LipschitzOnWith (1 / 1024 : ℝ≥0) (V p) (closedBall (ell : ℂ) (1 / 100))

namespace Data

variable (D : Data K u ell) {V : E → ℂ → H →L[ℂ] H} {U : Set E}
variable (P : PerturbationData V U ell)

include D P in
theorem contractionData : AnalyticFixedPoint.Data (scalarMap K u ell V) U
    (ell : ℂ) (1 / 100) (1 / 4) where
  radius_pos := by norm_num
  constant_lt_one := by norm_num
  maps := by
    intro p hp e he
    rw [mem_closedBall, dist_eq_norm] at he ⊢
    exact (D.rootMap_center_bound (V p e) e (P.small p hp e (by
      simpa only [mem_closedBall, dist_eq_norm] using he)) he).trans (by norm_num)
  lipschitz := by
    intro p hp
    apply LipschitzOnWith.of_dist_le_mul
    intro e he f hf
    have he' : ‖e - (ell : ℂ)‖ ≤ 1 / 100 := by
      simpa only [mem_closedBall, dist_eq_norm] using he
    have hf' : ‖f - (ell : ℂ)‖ ≤ 1 / 100 := by
      simpa only [mem_closedBall, dist_eq_norm] using hf
    have h := D.rootMap_sub_norm_le (V p e) (V p f) e f
      (P.small p hp e he) (P.small p hp f hf) he' hf'
    have hv := (P.energy_lipschitz p hp).dist_le_mul e he f hf
    simp only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at hv ⊢
    change ‖rootMap K u ell (V p e) e - rootMap K u ell (V p f) f‖ ≤ _
    nlinarith [norm_nonneg (e - f)]

def bandRoot (p : E) : ℂ := (D.contractionData P).point p

theorem bandRoot_mem (p : E) (hp : p ∈ U) :
    D.bandRoot P p ∈ closedBall (ell : ℂ) (1 / 100) :=
  (D.contractionData P).point_mem p hp

theorem bandRoot_fixed (p : E) (hp : p ∈ U) :
    rootMap K u ell (V p (D.bandRoot P p)) (D.bandRoot P p) = D.bandRoot P p :=
  (D.contractionData P).point_fixed p hp

theorem bandRoot_center_bound (p : E) (hp : p ∈ U) :
    ‖D.bandRoot P p - (ell : ℂ)‖ ≤ 1 / 200 := by
  have hmem := D.bandRoot_mem P p hp
  have he : ‖D.bandRoot P p - (ell : ℂ)‖ ≤ 1 / 100 := by
    simpa only [mem_closedBall, dist_eq_norm] using hmem
  have h := D.rootMap_center_bound (V p (D.bandRoot P p)) (D.bandRoot P p)
    (P.small p hp _ hmem) he
  rwa [D.bandRoot_fixed P p hp] at h

theorem kernel_nonzero_iff_bandRoot (p : E) (hp : p ∈ U) (e : ℂ)
    (he : e ∈ closedBall (ell : ℂ) (1 / 100)) :
    (∃ x : H, x ≠ 0 ∧ operator K (V p e) e x = 0) ↔ e = D.bandRoot P p := by
  rw [D.kernel_nonzero_iff_fixed (V p e) e (P.small p hp e he) (by
    simpa only [mem_closedBall, dist_eq_norm] using he)]
  constructor
  · intro h
    exact (D.contractionData P).point_unique p hp he h
  · rintro rfl
    exact D.bandRoot_fixed P p hp

def bandVector (p : E) : H := eigenvectorLift K u ell (V p (D.bandRoot P p)) (D.bandRoot P p)

theorem bandVector_ne_zero (p : E) : D.bandVector P p ≠ 0 := D.eigenvectorLift_ne_zero _ _

theorem bandVector_kernel (p : E) (hp : p ∈ U) :
    operator K (V p (D.bandRoot P p)) (D.bandRoot P p) (D.bandVector P p) = 0 := by
  have hm := D.bandRoot_mem P p hp
  rw [bandVector, D.operator_eigenvectorLift _ _ (P.small p hp _ hm) (by
    simpa only [mem_closedBall, dist_eq_norm] using hm), D.bandRoot_fixed P p hp,
    sub_self, zero_smul]

theorem bandRoot_kernel_finrank (p : E) (hp : p ∈ U) :
    Module.finrank ℂ (operator K (V p (D.bandRoot P p)) (D.bandRoot P p)).ker = 1 := by
  have hm := D.bandRoot_mem P p hp
  exact D.kernel_finrank_one _ _ (P.small p hp _ hm) (by
    simpa only [mem_closedBall, dist_eq_norm] using hm) (D.bandRoot_fixed P p hp)

#print axioms contractionData
#print axioms kernel_nonzero_iff_bandRoot
#print axioms bandRoot_kernel_finrank

end Data
end Maxwell.Continuum.RankOneBand
