import Maxwell.Continuum.ChebyshevWaveAnalytic
import Maxwell.Continuum.CalibrationGridPhase

/-! Rational evaluation of angular plane-wave samples with logarithmic guard precision. -/

namespace Maxwell.Continuum.Profile

open Maxwell.Certificate Calibration

theorem cosTurnApprox_center_bound (q : ℚ) (Q P : ℕ) (hq : |q| ≤ Q) :
    |(cosTurnApprox q Q P).center| ≤ 2 := by
  have hc := cosTurnApprox_contains q Q P hq
  rw [Ball.Contains, cosTurnApprox_radius] at hc
  push_cast at hc
  have hp : (1/2 : ℝ)^P ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht := abs_sub_le ((cosTurnApprox q Q P).center : ℝ) (Real.cos (2*Real.pi*(q : ℝ))) 0
  simp only [sub_zero, abs_sub_comm _ (Real.cos _)] at ht
  have hb : |((cosTurnApprox q Q P).center : ℝ)| ≤ 2 := by linarith [Real.abs_cos_le_one (2*Real.pi*(q : ℝ))]
  exact_mod_cast hb

def waveArgument (q : ℚ) (Q P : ℕ) (s : ℚ) : ℚ :=
  q*(cosTurnApprox s 1 (phaseBits Q (P+4))).center

theorem waveArgument_bound (q s : ℚ) (Q P : ℕ) (hq : |q| ≤ Q) (hs : |s| ≤ 1) :
    |waveArgument q Q P s| ≤ (2*(Q+1) : ℕ) := by
  rw [waveArgument, abs_mul]
  have hc := cosTurnApprox_center_bound s 1 (phaseBits Q (P+4)) (by simpa using hs)
  have h := mul_le_mul hq hc (abs_nonneg _) (Nat.cast_nonneg Q : (0 : ℚ)≤Q)
  push_cast
  nlinarith only [h]

theorem waveArgument_error (q s : ℚ) (Q P : ℕ) (hq : |q| ≤ Q) (hs : |s| ≤ 1) :
    |2*Real.pi*(q : ℝ)*Real.cos (2*Real.pi*(s : ℝ))-2*Real.pi*(waveArgument q Q P s : ℝ)| ≤
      (1/2 : ℝ)^(P+5) := by
  have hc := cosTurnApprox_contains s 1 (phaseBits Q (P+4)) (by simpa using hs)
  rw [Ball.Contains, cosTurnApprox_radius] at hc
  push_cast at hc
  have hqr : |(q : ℝ)| ≤ Q := by exact_mod_cast hq
  have hg := phase_guard Q (P+4)
  calc
    _ = 2*Real.pi*|(q : ℝ)| * |Real.cos (2*Real.pi*(s : ℝ))-
        ((cosTurnApprox s 1 (phaseBits Q (P+4))).center : ℝ)| := by
      simp only [waveArgument, Rat.cast_mul]
      rw [show 2*Real.pi*(q : ℝ)*Real.cos (2*Real.pi*(s : ℝ))-
        2*Real.pi*((q : ℝ)*((cosTurnApprox s 1 (phaseBits Q (P+4))).center : ℝ))=
        (2*Real.pi*(q : ℝ))*(Real.cos (2*Real.pi*(s : ℝ))-
          ((cosTurnApprox s 1 (phaseBits Q (P+4))).center : ℝ)) by ring]
      simp only [abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ)<2)]
    _ ≤ 8*(Q : ℝ)*(1/2 : ℝ)^phaseBits Q (P+4) := by
      gcongr
      linarith [Real.pi_lt_four]
    _ ≤ 4*(1/2 : ℝ)^((P+4)+3) := by linarith only [hg]
    _ = _ := by
      rw [show (P+4)+3=(P+5)+2 by omega, pow_add]
      ring

def waveSample (q : ℚ) (Q P : ℕ) (s : ℚ) : ComplexRectangle :=
  ⟨⟨(cosTurnApprox (waveArgument q Q P s) (2*(Q+1)) (P+4)).center,(1/2)^P,by positivity⟩,
   ⟨(sinTurnApprox (waveArgument q Q P s) (2*(Q+1)) (P+4)).center,(1/2)^P,by positivity⟩⟩

theorem waveSample_contains (q s : ℚ) (Q P : ℕ) (hq : |q| ≤ Q) (hs : |s| ≤ 1) :
    (waveSample q Q P s).Contains (waveAngular (2*Real.pi*(q : ℝ)) (2*Real.pi*(s : ℝ))) := by
  have hb := waveArgument_bound q s Q P hq hs
  have he := waveArgument_error q s Q P hq hs
  have ha : Complex.I*((2*Real.pi*(q : ℝ) : ℝ) : ℂ)*(Real.cos (2*Real.pi*(s : ℝ)) : ℂ)=
      ((2*Real.pi*(q : ℝ)*Real.cos (2*Real.pi*(s : ℝ)) : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [waveAngular, ha]
  have budget : (1/2 : ℝ)^(P+5)+(1/2 : ℝ)^(P+4) ≤ (1/2 : ℝ)^P := by
    rw [pow_add, pow_add]
    nlinarith only [pow_nonneg (by norm_num : (0 : ℝ)≤1/2) P]
  constructor
  · have hc := cosTurnApprox_contains (waveArgument q Q P s) (2*(Q+1)) (P+4) hb
    rw [Ball.Contains, cosTurnApprox_radius] at hc
    push_cast at hc
    have hd := (Real.abs_cos_sub_cos_le
      (2*Real.pi*(q : ℝ)*Real.cos (2*Real.pi*(s : ℝ))) (2*Real.pi*(waveArgument q Q P s : ℝ))).trans he
    change |(Complex.exp _).re-((cosTurnApprox (waveArgument q Q P s) (2*(Q+1)) (P+4)).center : ℝ)| ≤ _
    rw [Complex.exp_ofReal_mul_I_re]
    change _ ≤ (((1/2 : ℚ)^P : ℚ) : ℝ)
    push_cast
    exact (abs_sub_le _ (Real.cos (2*Real.pi*(waveArgument q Q P s : ℝ))) _).trans (by linarith)
  · have hc := sinTurnApprox_contains (waveArgument q Q P s) (2*(Q+1)) (P+4) hb
    rw [Ball.Contains, sinTurnApprox_radius] at hc
    push_cast at hc
    have hd := (Real.abs_sin_sub_sin_le
      (2*Real.pi*(q : ℝ)*Real.cos (2*Real.pi*(s : ℝ))) (2*Real.pi*(waveArgument q Q P s : ℝ))).trans he
    change |(Complex.exp _).im-((sinTurnApprox (waveArgument q Q P s) (2*(Q+1)) (P+4)).center : ℝ)| ≤ _
    rw [Complex.exp_ofReal_mul_I_im]
    change _ ≤ (((1/2 : ℚ)^P : ℚ) : ℝ)
    push_cast
    exact (abs_sub_le _ (Real.sin (2*Real.pi*(waveArgument q Q P s : ℝ))) _).trans (by linarith)

theorem waveSample_error (q s : ℚ) (Q P : ℕ) (hq : |q| ≤ Q) (hs : |s| ≤ 1) :
    ‖waveAngular (2*Real.pi*(q : ℝ)) (2*Real.pi*(s : ℝ))-rectangleCenter (waveSample q Q P s)‖ ≤
      2*(1/2 : ℝ)^P := by
  have h := rectangle_center_error (waveSample_contains q s Q P hq hs)
  change _ ≤ (((1/2 : ℚ)^P : ℚ) : ℝ)+(((1/2 : ℚ)^P : ℚ) : ℝ) at h
  push_cast at h
  linarith

#print axioms waveSample_error

end Maxwell.Continuum.Profile
