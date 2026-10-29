import Maxwell.Continuum.RankOneBandFamily

/-! Uniform perturbation control of the actual constructed band root. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand.Data

set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {E : Type*} {K : H →L[ℂ] H} {u : H} {ell : ℝ}
variable (D : Data K u ell) {V W : E → ℂ → H →L[ℂ] H} {U : Set E}
variable (P : PerturbationData V U ell) (Q : PerturbationData W U ell)

theorem bandRoot_sub_bound (p : E) (hp : p ∈ U) {ε : ℝ} (hε : 0 ≤ ε)
    (hVW : ∀ e ∈ closedBall (ell : ℂ) (1 / 100), ‖V p e - W p e‖ ≤ ε) :
    ‖D.bandRoot P p - D.bandRoot Q p‖ ≤ 4 * ε := by
  have hm := D.bandRoot_mem Q p hp
  have he : ‖D.bandRoot Q p - (ell : ℂ)‖ ≤ 1 / 100 := by
    simpa only [mem_closedBall, dist_eq_norm] using hm
  have hdist : dist (scalarMap K u ell V p (D.bandRoot Q p))
      (scalarMap K u ell W p (D.bandRoot Q p)) ≤ 2 * ε := by
    have h := D.rootMap_sub_norm_le (V p (D.bandRoot Q p)) (W p (D.bandRoot Q p))
      (D.bandRoot Q p) (D.bandRoot Q p) (P.small p hp _ hm) (Q.small p hp _ hm) he he
    simp only [sub_self, norm_zero, mul_zero, add_zero] at h
    simpa only [dist_eq_norm, scalarMap] using
      h.trans (mul_le_mul_of_nonneg_left (hVW _ hm) (by norm_num))
  have h := (D.contractionData P).perturbation_bound p hp hm
    (G := scalarMap K u ell W) (D.bandRoot_fixed Q p hp) hdist
  change dist (D.bandRoot P p) (D.bandRoot Q p) ≤ _ at h
  rw [dist_eq_norm] at h
  norm_num at h
  linarith

theorem bandRoot_eq_of_eq (p : E) (hp : p ∈ U)
    (hVW : ∀ e ∈ closedBall (ell : ℂ) (1 / 100), V p e = W p e) :
    D.bandRoot P p = D.bandRoot Q p := by
  have h := D.bandRoot_sub_bound P Q p hp (ε := 0) (by rfl)
    (fun e he => by rw [hVW e he, sub_self, norm_zero])
  simpa only [mul_zero, norm_le_zero_iff, sub_eq_zero] using h

theorem bandVector_sub_unit_bound (p : E) (hp : p ∈ U) :
    ‖D.bandVector P p - u‖ ≤ 5 / 32 := by
  have hm := D.bandRoot_mem P p hp
  have h := D.correctionVector_norm_le (V p (D.bandRoot P p)) (D.bandRoot P p)
    (P.small p hp _ hm) (by simpa only [mem_closedBall, dist_eq_norm] using hm)
  have hs := P.small p hp _ hm
  simpa only [bandVector, eigenvectorLift, add_sub_cancel_left] using
    h.trans (show 40 * ‖V p (D.bandRoot P p)‖ ≤ 5 / 32 by linarith)

theorem bandVector_norm_le (p : E) (hp : p ∈ U) : ‖D.bandVector P p‖ ≤ 2 := by
  have hm := D.bandRoot_mem P p hp
  exact D.eigenvectorLift_norm_le _ _ (P.small p hp _ hm) (by
    simpa only [mem_closedBall, dist_eq_norm] using hm)

#print axioms bandRoot_sub_bound
#print axioms bandVector_sub_unit_bound

end Maxwell.Continuum.RankOneBand.Data
