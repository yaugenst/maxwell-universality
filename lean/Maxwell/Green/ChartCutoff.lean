import Maxwell.Green.ChartVolume
import Maxwell.Green.CauchyRegularData
import Maxwell.Green.SmoothLocalization

/-! Actual product cutoffs in the principal coordinates, transported to the
physical torus. Their smoothness, core and support are proved here. -/

noncomputable section

namespace Maxwell.Green

open MeasureTheory Filter Metric Set WithLp
open scoped Topology ContDiff

def principalCutoff (T : (ℂ × ℝ) ≃L[ℝ] RealTorusCoordinates)
    (ψ : ℂ → ℝ) (ρ : ℝ) (q : RealTorusCoordinates) : ℝ :=
  ψ (T.symm q).1 * scaledPoleCutoff ρ (T.symm q).2

@[simp] theorem principalCutoff_chart (T : (ℂ × ℝ) ≃L[ℝ] RealTorusCoordinates)
    (ψ : ℂ → ℝ) (ρ : ℝ) (z : ℂ × ℝ) :
    principalCutoff T ψ ρ (T z) = ψ z.1 * scaledPoleCutoff ρ z.2 := by
  simp [principalCutoff]

theorem principalCutoff_contDiff (T : (ℂ × ℝ) ≃L[ℝ] RealTorusCoordinates)
    (ψ : ℂ → ℝ) (ρ : ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (principalCutoff T ψ ρ) := by
  apply (hψ.comp (contDiff_fst.comp T.symm.contDiff)).mul
  exact (unitPoleCutoff_contDiff.comp (contDiff_id.div_const ρ)).comp
    (contDiff_snd.comp T.symm.contDiff)

theorem principalCutoff_one_near_zero (T : (ℂ × ℝ) ≃L[ℝ] RealTorusCoordinates)
    (ψ : ℂ → ℝ) {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (hψ : ∀ w, ‖w‖ < δ → ψ w = 1) :
    principalCutoff T ψ ρ =ᶠ[𝓝 (0 : RealTorusCoordinates)] fun _ => 1 := by
  have hw : ∀ᶠ q in 𝓝 (0 : RealTorusCoordinates), ‖(T.symm q).1‖ < δ := by
    have hc := (continuous_fst.comp T.symm.continuous).norm.continuousAt (x := 0)
    exact hc.eventually (gt_mem_nhds (by simpa using hδ))
  have hu : ∀ᶠ q in 𝓝 (0 : RealTorusCoordinates), |(T.symm q).2| < ρ := by
    have hc := (continuous_snd.comp T.symm.continuous).abs.continuousAt (x := 0)
    exact hc.eventually (gt_mem_nhds (by simpa using hρ))
  filter_upwards [hw, hu] with q hw hu
  simp [principalCutoff, hψ _ hw, scaledPoleCutoff_eq_one hρ hu.le]

theorem realPrincipalChart_norm_le (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (w : ℂ) (u : ℝ) :
    ‖realPrincipalChart v b (w, u)‖ ≤ 2 * ‖w‖ + |u| := by
  have hb₀ : ‖(b 0 : MomentumSpace)‖ = 1 := b.norm_eq_one 0
  have hb₁ : ‖(b 1 : MomentumSpace)‖ = 1 := b.norm_eq_one 1
  calc
    _ ≤ (‖w.re • (b 0 : MomentumSpace)‖ + ‖w.im • (b 1 : MomentumSpace)‖) +
        ‖u • propagationNormal v‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = |w.re| + |w.im| + |u| := by
      simp only [norm_smul, Real.norm_eq_abs, hb₀, hb₁, propagationNormal_norm v hv, mul_one]
    _ ≤ _ := by linarith [Complex.abs_re_le_norm w, Complex.abs_im_le_norm w]

theorem principalCutoff_tsupport_coordinates
    (T : (ℂ × ℝ) ≃L[ℝ] RealTorusCoordinates) (ψ : ℂ → ℝ)
    {ρ η : ℝ} (hρ : 0 < ρ) (hψ : ∀ w, ψ w ≠ 0 → ‖w‖ ≤ η) :
    tsupport (principalCutoff T ψ ρ) ⊆
      {q | ‖(T.symm q).1‖ ≤ η ∧ |(T.symm q).2| ≤ 2 * ρ} := by
  apply closure_minimal
  · intro q hq
    have hψq : ψ (T.symm q).1 ≠ 0 := fun h => hq (by simp [principalCutoff, h])
    have hχq : scaledPoleCutoff ρ (T.symm q).2 ≠ 0 := fun h => hq (by simp [principalCutoff, h])
    refine ⟨hψ _ hψq, ?_⟩
    by_contra hn
    exact hχq (scaledPoleCutoff_eq_zero hρ (le_of_not_ge hn))
  · exact (isClosed_le (continuous_fst.comp T.symm.continuous).norm continuous_const).inter
      (isClosed_le (continuous_snd.comp T.symm.continuous).abs continuous_const)

/-- Choosing the two coordinate radii small enough places the entire
closed cutoff support strictly inside the fundamental torus cube. -/
theorem principalCutoff_tsupport_interior
    (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (ψ : ℂ → ℝ)
    {ρ η : ℝ} (hρ : 0 < ρ) (hψ : ∀ w, ψ w ≠ 0 → ‖w‖ ≤ η)
    (hsmall : 2 * η + 2 * ρ < Real.pi) :
    tsupport (principalCutoff (coordinatePrincipalLinearEquiv v hv b) ψ ρ) ⊆
      interior (torusCube (-Real.pi) (2 * Real.pi)) := by
  let T := coordinatePrincipalLinearEquiv v hv b
  intro q hq
  obtain ⟨hw, hu⟩ := principalCutoff_tsupport_coordinates T ψ hρ hψ hq
  let z := T.symm q
  have hnorm : ‖realPrincipalChart v b z‖ < Real.pi :=
    (realPrincipalChart_norm_le v hv b z.1 z.2).trans_lt
      ((by linarith : 2 * ‖z.1‖ + |z.2| ≤ 2 * η + 2 * ρ).trans_lt hsmall)
  rw [interior_torusCube]
  intro i
  have hqi : |q i| < Real.pi := by
    have he : q = ofLp (realPrincipalChart v b z) := by
      change q = T (T.symm q)
      exact (T.apply_symm_apply q).symm
    rw [he]
    exact (PiLp.norm_apply_le (realPrincipalChart v b z) i).trans_lt hnorm
  have h := abs_lt.mp hqi
  exact ⟨h.1, by linarith [h.2]⟩

/-- Multiplication by the cutoff requires regularity of the original
quotient only on its closed support. -/
theorem contDiffAt_principalCutoff_mul
    (T : (ℂ × ℝ) ≃L[ℝ] RealTorusCoordinates) (ψ : ℂ → ℝ) (ρ : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (P : RealTorusCoordinates → ℂ) (q : RealTorusCoordinates)
    (hP : q ∈ tsupport (principalCutoff T ψ ρ) → ContDiffAt ℝ ∞ P q) :
    ContDiffAt ℝ ∞ (fun q => (principalCutoff T ψ ρ q : ℂ) * P q) q := by
  by_cases hq : q ∈ tsupport (principalCutoff T ψ ρ)
  · exact ((Complex.ofRealCLM.contDiff.comp (principalCutoff_contDiff T ψ ρ hψ)).contDiffAt).mul (hP hq)
  · apply (show ContDiffAt ℝ ∞ (fun _ : RealTorusCoordinates => (0 : ℂ)) q from
      contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hq] with x hx
    simp only [hx, Pi.zero_apply, Complex.ofReal_zero, zero_mul]

end Maxwell.Green
