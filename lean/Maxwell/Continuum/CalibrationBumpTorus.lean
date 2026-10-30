import Maxwell.Continuum.PeriodicEuclideanFourier
import Maxwell.Continuum.WellFourierDecay
import Maxwell.Continuum.CalibrationImageGeometry
import Maxwell.Continuum.CalibrationLatticeTail

/-! The actual compact well root on a finite torus, with exact
continuum Fourier coefficients and decay at the rescaled frequency. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open Well Bloch OperatorFourier PeriodicSampling UnitAddTorus

def scaledRoot (s : ℝ) (x : Fin 3 → ℝ) : ℂ := (qw (s • WithLp.toLp 2 x) : ℂ)

theorem scaledRoot_continuous (s : ℝ) : Continuous (scaledRoot s) := by
  have hi : Continuous (fun x : Fin 3 → ℝ => s • (WithLp.toLp 2 x : Space)) := by fun_prop
  exact Complex.continuous_ofReal.comp (qw_contDiff.continuous.comp hi)

theorem scaledRoot_zero {s : ℝ} (hs : 4 ≤ s) (x : Fin 3 → ℝ)
    (hx : ∃ i, (1/4 : ℝ) ≤ |x i|) : scaledRoot s x = 0 := by
  obtain ⟨i, hi⟩ := hx
  have hc : |s*x i| ≤ ‖s • (WithLp.toLp 2 x : Space)‖ :=
    PiLp.norm_apply_le (s • (WithLp.toLp 2 x : Space)) i
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ s)] at hc
  have hn : 1 ≤ ‖s • (WithLp.toLp 2 x : Space)‖ := by nlinarith
  simp only [scaledRoot, (qw_zero_iff _).mpr hn, Complex.ofReal_zero]

def rootTorus (s : ℝ) (hs : 4 ≤ s) : C(UnitAddTorus (Fin 3), ℂ) :=
  centeredContinuousLift (scaledRoot s) (scaledRoot_continuous s) (scaledRoot_zero hs)

theorem rootTorus_norm_le_one (s : ℝ) (hs : 4 ≤ s) (x : UnitAddTorus (Fin 3)) :
    ‖rootTorus s hs x‖ ≤ 1 := by
  change ‖(qw _ : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (qw_nonneg _)]
  exact qw_le_one _

theorem rootTorus_coefficient (s : ℝ) (hs : 4 ≤ s) (n : Bloch.Alias) :
    mFourierCoeff (rootTorus s hs) n =
      (s^3)⁻¹ • rawPhysicalFourier qw ((2*Real.pi/s) • integerVector n) := by
  rw [rootTorus, centeredLift_coefficient (scaledRoot s) (scaledRoot_continuous s) (scaledRoot_zero hs)]
  exact euclidean_scaled_coefficient (complexify qw) s (by linarith) n

theorem integerVector_norm_ge_radius (n : Bloch.Alias) :
    (imageRadius n : ℝ) ≤ ‖integerVector n‖ := by
  obtain ⟨i, hi⟩ := imageRadius_attained n
  rw [← hi]
  exact PiLp.norm_apply_le (integerVector n) i

def rootDecayRate (s : ℝ) : ℝ := Real.sqrt (2*Real.pi/s)/64

theorem rootDecayRate_pos {s : ℝ} (hs : 0 < s) : 0 < rootDecayRate s := by
  unfold rootDecayRate
  positivity

theorem rootTorus_coefficient_decay (s : ℝ) (hs : 4 ≤ s) (n : Bloch.Alias) :
    ‖mFourierCoeff (rootTorus s hs) n‖ ≤
      24/(s^3)*Real.exp (-rootDecayRate s*Real.sqrt (imageRadius n)) := by
  have hs0 : 0 < s := by linarith
  have hp : 0 < 2*Real.pi/s := by positivity
  rw [rootTorus_coefficient, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (s^3)⁻¹)]
  have hd := rawPhysicalFourier_decay qw qw_contDiff qw_hasCompactSupport (by rw [qw_tsupport])
    (fun K y v hv => qw_directional_gevrey y v hv K) ((2*Real.pi/s) • integerVector n)
  have hr : (2*Real.pi/s)*(imageRadius n : ℝ) ≤ ‖(2*Real.pi/s) • integerVector n‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left (integerVector_norm_ge_radius n) hp.le
  have he : Real.exp (-Real.sqrt ‖(2*Real.pi/s) • integerVector n‖/64) ≤
      Real.exp (-rootDecayRate s*Real.sqrt (imageRadius n)) := by
    apply Real.exp_le_exp.mpr
    have ht := Real.sqrt_le_sqrt hr
    rw [Real.sqrt_mul hp.le] at ht
    dsimp [rootDecayRate]
    linarith
  calc
    _ ≤ (s^3)⁻¹*(24*Real.exp (-Real.sqrt ‖(2*Real.pi/s) • integerVector n‖/64)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ (s^3)⁻¹*(24*Real.exp (-rootDecayRate s*Real.sqrt (imageRadius n))) := by gcongr
    _ = _ := by ring

#print axioms rootTorus_coefficient
#print axioms rootTorus_coefficient_decay

end Maxwell.Continuum.Calibration
