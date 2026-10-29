import Maxwell.Green.CauchyRegularData

/-! Exact identification of the localized original quotient with the pole
and regular integrals appearing in the scalar asymptotic theorem. -/

noncomputable section

namespace Maxwell.Green

open MeasureTheory Filter Complex Metric
open scoped Topology

def localizedQuotientIntegral (D : LocalSaddleData) (A F : ℂ → ℂ → ℂ)
    (ρ T : ℝ) : ℂ :=
  ∫ w : ℂ, ∫ u : ℝ, Complex.exp (I * (T : ℂ) * u) *
    (D.cutoff w : ℂ) * (scaledPoleCutoff ρ u : ℂ) * (A w u / F w u)

theorem RegularNormalData.integrable_oscillatory_amplitude (R : RegularNormalData)
    (T : ℝ) (w : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (I * (T : ℂ) * u) * R.amplitude w u) := by
  have hc : Continuous (R.amplitude w) :=
    continuous_iff_continuousAt.mpr fun u => (R.derivative w u).continuousAt
  exact integrable_oscillatory_mul T (hc.integrable_of_hasCompactSupport (R.compact w))

theorem LocalSaddleData.integrable_localizedPoleKernel (D : LocalSaddleData)
    {ρ : ℝ} (hρ : 0 < ρ) (T : ℝ) {w : ℂ} (hw : w ≠ 0) :
    Integrable (D.localizedPoleKernel ρ T w) := by
  by_cases hc : D.cutoff w = 0
  · change Integrable (fun u => D.localizedPoleKernel ρ T w u)
    simp only [LocalSaddleData.localizedPoleKernel, LocalSaddleData.poleWeight, hc,
      Complex.ofReal_zero, zero_mul]
    exact integrable_zero _ _ _
  · exact (integrable_localized_pole _ (scaledPoleCutoff_complex_contDiff ρ).continuous
      (scaledPoleCutoff_complex_hasCompactSupport hρ) (D.phase_im_pos hw hc) T).const_mul _

/-- Cauchy's exact simple-pole formula identifies the original localized
quotient. The only discarded fiber is the null transverse origin. -/
theorem localizedQuotientIntegral_eq (D : LocalSaddleData) (R : RegularNormalData)
    (A F : ℂ → ℂ → ℂ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : 4 * ρ ≤ r)
    (hs : HasCompactSupport D.cutoff)
    (hp : ∀ w, D.cutoff w ≠ 0 → ‖D.phase w‖ ≤ ρ / 2)
    (hA : ∀ w, D.cutoff w ≠ 0 → AnalyticOnNhd ℂ (A w) (closedBall 0 r))
    (hF : ∀ w, D.cutoff w ≠ 0 → AnalyticOnNhd ℂ (F w) (closedBall 0 r))
    (hroot : ∀ w, D.cutoff w ≠ 0 → F w (D.phase w) = 0)
    (hsimple : ∀ w, D.cutoff w ≠ 0 → deriv (F w) (D.phase w) ≠ 0)
    (hunique : ∀ w, D.cutoff w ≠ 0 → ∀ z ∈ closedBall 0 r,
      F w z = 0 → z = D.phase w)
    (hamp : ∀ w, D.cutoff w ≠ 0 → D.amplitude w =
      A w (D.phase w) / deriv (F w) (D.phase w))
    (hreg : ∀ w u, R.amplitude w u = (D.cutoff w : ℂ) * (scaledPoleCutoff ρ u : ℂ) *
      normalCauchyRemainder (A w) (F w) 0 r (u : ℂ))
    {T : ℝ} (hT : 0 < T) :
    localizedQuotientIntegral D A F ρ T = localGreenIntegral D R ρ T := by
  have hr : 0 < r := by linarith
  have heq : ∀ w : ℂ, w ≠ 0 → ∀ u : ℝ,
      Complex.exp (I * (T : ℂ) * u) * (D.cutoff w : ℂ) *
        (scaledPoleCutoff ρ u : ℂ) * (A w u / F w u) =
      D.localizedPoleKernel ρ T w u + Complex.exp (I * (T : ℂ) * u) * R.amplitude w u := by
    intro w hw u
    by_cases hc : D.cutoff w = 0
    · simp [LocalSaddleData.localizedPoleKernel, LocalSaddleData.poleWeight, hreg, hc]
    by_cases hu : scaledPoleCutoff ρ u = 0
    · simp [LocalSaddleData.localizedPoleKernel, hreg, hu]
    have hup : (u : ℂ) ≠ D.phase w := by
      intro he
      have hi := D.phase_im_pos hw hc
      rw [← he, Complex.ofReal_im] at hi
      exact (lt_irrefl 0 hi)
    have hpu : D.phase w ∈ ball (0 : ℂ) r := by
      rw [mem_ball, dist_zero_right]
      exact (hp w hc).trans_lt (by linarith)
    have huu : (u : ℂ) ∈ ball (0 : ℂ) r := by
      have hcu : (u : ℝ) ∈ tsupport (fun u : ℝ => (scaledPoleCutoff ρ u : ℂ)) :=
        subset_tsupport _ (Complex.ofReal_ne_zero.mpr hu)
      have hb := scaledPoleCutoff_complex_half_disk hρ hρr u hcu
      rw [sub_zero] at hb
      rw [mem_ball, dist_zero_right]
      exact hb.trans_lt (by linarith)
    rw [simple_pole_cauchy_remainder (hA w hc) (hF w hc) hpu huu hup
      (hroot w hc) (hsimple w hc) (hunique w hc), ← hamp w hc,
      LocalSaddleData.localizedPoleKernel, LocalSaddleData.poleWeight, hreg]
    ring
  obtain ⟨C, hC, hb⟩ := D.exists_normalPole_error_bound ρ hρ
    (D.poleWeight_integrable_of_compact hs) hp
  have hiP := (hb T hT).2.1
  have hiR := (R.integral_bound hT).1
  unfold localizedQuotientIntegral localGreenIntegral
  calc
    _ = ∫ w : ℂ, (∫ u : ℝ, D.localizedPoleKernel ρ T w u) +
        ∫ u : ℝ, Complex.exp (I * (T : ℂ) * u) * R.amplitude w u := by
      apply integral_congr_ae
      filter_upwards [volume.ae_ne (0 : ℂ)] with w hw
      simp_rw [heq w hw]
      exact integral_add (D.integrable_localizedPoleKernel hρ T hw)
        (R.integrable_oscillatory_amplitude T w)
    _ = _ := integral_add hiP hiR

end Maxwell.Green
