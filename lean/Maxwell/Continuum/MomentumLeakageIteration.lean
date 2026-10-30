import Maxwell.Continuum.MomentumLeakageStep
import Maxwell.Continuum.AuxiliaryMomentumError

/-! Finite nested-cutoff iteration, retaining the actual momentum
projection and exact geometric contraction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open PeriodicBand

attribute [local irreducible] highMomentumProjection Auxiliary.resolvent

theorem quarter_iteration (a : ℕ → ℝ) (B C : ℝ) (hC : 0 ≤ C) (K : ℕ)
    (hzero : a 0 ≤ B) (hstep : ∀ k < K, a (k+1) ≤ (1/4 : ℝ)*a k+C) :
    a K ≤ (1/4 : ℝ)^K * B + 2*C := by
  have hi : ∀ n ≤ K, a n ≤ (1/4 : ℝ)^n * B+2*C := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa only [pow_zero, one_mul] using hzero.trans (by linarith : B ≤ B+2*C)
    | succ n ih =>
      intro hn
      have hh := hstep n (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn)
      have hi := ih (Nat.le_trans (Nat.le_succ n) hn)
      rw [pow_succ]
      nlinarith
  exact hi K le_rfl

variable {ι : Type*} [Fintype ι]

theorem finiteWell_nested_bound {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (hh : h ≤ 1/(2 : ℝ)^1024)
    (x : ι → Space) (v : ι → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ (2 : ℝ)^130*h^2)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (x i) h⁻¹) (Metric.ball (x j) h⁻¹))
    (f g : FieldL2) (heq : f = g + finiteWellOperator h x v (resolvent D hσ0 hσ f))
    (a Δ G : ℝ) (ha : smallRadius/4 ≤ a) (hΔ : 0 ≤ Δ) (hG : 0 ≤ G)
    (hsource : ∀ s : ℝ, a ≤ s → ‖highMomentumProjection s g‖ ≤ G) (K : ℕ) :
    ‖highMomentumProjection (a+(K : ℝ)*Δ) f‖ ≤ (1/4 : ℝ)^K * ‖f‖ +
      2*(G+((2 : ℝ)^232*(Fintype.card ι : ℝ)*Real.exp (-Real.sqrt (Δ/h)/512))*‖f‖) := by
  apply quarter_iteration (fun k => ‖highMomentumProjection (a+(k : ℝ)*Δ) f‖) ‖f‖
    (G+((2 : ℝ)^232*(Fintype.card ι : ℝ)*Real.exp (-Real.sqrt (Δ/h)/512))*‖f‖)
    (by positivity) K
  · simpa only [Nat.cast_zero, zero_mul, add_zero, one_mul] using
      (highMomentumProjection a).le_of_opNorm_le (highMomentumProjection_norm_le a) f
  · intro k _
    have hr : smallRadius/4 ≤ a+(k : ℝ)*Δ := ha.trans (le_add_of_nonneg_right (by positivity))
    have hs : a ≤ a+((k+1 : ℕ) : ℝ)*Δ := le_add_of_nonneg_right (by positivity)
    have hb := finiteWell_projection_step D hσ0 hσ hh x v hv0 hv hdisj f g heq
      (a+((k+1 : ℕ) : ℝ)*Δ) (a+(k : ℝ)*Δ) hr
    have hd : a+((k+1 : ℕ) : ℝ)*Δ-(a+(k : ℝ)*Δ) = Δ := by push_cast; ring
    rw [hd] at hb
    have hsrc := hsource _ hs
    linarith

#print axioms finiteWell_nested_bound

end Maxwell.Continuum.Auxiliary
