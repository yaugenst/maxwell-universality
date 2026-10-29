import Maxwell.Continuum.WellFourierDeriv
import Maxwell.Continuum.WellDecayOptimization

/-! Pointwise Fourier decay, including the angular-frequency and unitary normalization. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Set Metric
open scoped FourierTransform

def rawPhysicalFourier (f : Space → ℝ) (p : Space) : ℂ :=
  𝓕 (complexify f) ((2 * Real.pi)⁻¹ • p)

/-- The unitary angular-frequency convention in the continuum manuscript. -/
def physicalFourier (f : Space → ℝ) (p : Space) : ℂ :=
  (2 * Real.pi) ^ (-(3 / 2 : ℝ)) • rawPhysicalFourier f p

theorem physicalFourier_norm_le_raw (f : Space → ℝ) (p : Space) :
    ‖physicalFourier f p‖ ≤ ‖rawPhysicalFourier f p‖ := by
  have hc₀ : 0 ≤ (2 * Real.pi) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hc₁ : (2 * Real.pi) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)
  rw [physicalFourier, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc₀]
  nlinarith [norm_nonneg (rawPhysicalFourier f p)]

theorem rawPhysicalFourier_gevrey_bound (f : Space → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hs : tsupport f ⊆ closedBall (0 : Space) 1)
    (hb : ∀ (K : ℕ) (y v : Space), ‖v‖ ≤ 1 →
      |directionalDerivative K f y v| ≤ (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2)
    (p : Space) (K : ℕ) :
    ‖p‖ ^ K * ‖rawPhysicalFourier f p‖ ≤ 8 * (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by
  by_cases hp : p = 0
  · subst p
    cases K with
    | zero =>
      have h := fourier_directional_le f hf hfc 0 0 0
      have hh := integral_abs_directional_le f hs 0 0 1 (by norm_num)
        (fun y => by simpa using hb 0 y 0 (by simp))
      simpa [rawPhysicalFourier] using h.trans hh
    | succ K => simp
  · have hn : 0 < ‖p‖ := norm_pos_iff.mpr hp
    let v : Space := ‖p‖⁻¹ • p
    let ξ : Space := (2 * Real.pi)⁻¹ • p
    have hv : ‖v‖ ≤ 1 := by
      dsimp [v]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hip : 2 * Real.pi * |inner ℝ ξ v| = ‖p‖ := by
      dsimp [ξ, v]
      rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      rw [abs_of_nonneg (by positivity)]
      field_simp
    have h := fourier_directional_le f hf hfc K ξ v
    rw [hip] at h
    have hh := integral_abs_directional_le f hs K v
      ((400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2) (by positivity) (fun y => hb K y v hv)
    simpa only [rawPhysicalFourier, mul_assoc] using h.trans hh

theorem rawPhysicalFourier_decay (f : Space → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hs : tsupport f ⊆ closedBall (0 : Space) 1)
    (hb : ∀ (K : ℕ) (y v : Space), ‖v‖ ≤ 1 →
      |directionalDerivative K f y v| ≤ (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2)
    (p : Space) : ‖rawPhysicalFourier f p‖ ≤ 24 * Real.exp (-Real.sqrt ‖p‖ / 64) := by
  by_cases hp : p = 0
  · have h := rawPhysicalFourier_gevrey_bound f hf hfc hs hb p 0
    subst p
    norm_num at h ⊢
    linarith
  · exact gevrey_decay_optimization ‖p‖ ‖rawPhysicalFourier f p‖ (norm_pos_iff.mpr hp)
      (rawPhysicalFourier_gevrey_bound f hf hfc hs hb p)

theorem w_physicalFourier_decay (p : Space) :
    ‖physicalFourier w p‖ ≤ 24 * Real.exp (-Real.sqrt ‖p‖ / 64) :=
  (physicalFourier_norm_le_raw w p).trans
    (rawPhysicalFourier_decay w w_contDiff w_hasCompactSupport (by rw [w_tsupport])
      (fun K y v hv => w_directional_gevrey y v hv K) p)

theorem qw_physicalFourier_decay (p : Space) :
    ‖physicalFourier qw p‖ ≤ 24 * Real.exp (-Real.sqrt ‖p‖ / 64) :=
  (physicalFourier_norm_le_raw qw p).trans
    (rawPhysicalFourier_decay qw qw_contDiff qw_hasCompactSupport (by rw [qw_tsupport])
      (fun K y v hv => qw_directional_gevrey y v hv K) p)

theorem well_physicalFourier_decay (p : Space) :
    ‖physicalFourier w p‖ + ‖physicalFourier qw p‖ ≤
      (2 : ℝ) ^ 20 * Real.exp (-Real.sqrt ‖p‖ / 256) := by
  calc
    ‖physicalFourier w p‖ + ‖physicalFourier qw p‖ ≤
        48 * Real.exp (-Real.sqrt ‖p‖ / 64) := by
      linarith [w_physicalFourier_decay p, qw_physicalFourier_decay p]
    _ ≤ (2 : ℝ) ^ 20 * Real.exp (-Real.sqrt ‖p‖ / 256) := by
      have he : Real.exp (-Real.sqrt ‖p‖ / 64) ≤ Real.exp (-Real.sqrt ‖p‖ / 256) :=
        Real.exp_le_exp.mpr (by linarith [Real.sqrt_nonneg ‖p‖])
      exact mul_le_mul (by norm_num) he (Real.exp_pos _).le (by positivity)

end Maxwell.Continuum.Well
