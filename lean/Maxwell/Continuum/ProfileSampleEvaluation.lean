import Maxwell.Continuum.ProfileAngularGevrey
import Maxwell.Continuum.ProfileGlueEvaluation
import Maxwell.Continuum.PhaseEvaluation
import Maxwell.Continuum.ProfileDegree

/-! Explicit rational samples and dimensions of the finite profile encoder. -/

namespace Maxwell.Continuum.Profile

open Maxwell.Certificate

def profileWorkBits (N : ℕ) : ℕ := N+3*Nat.clog 2 (profileDegree N+1)+32
def profileGrid (N : ℕ) : ℕ := profileDegree N+profileDegree (profileWorkBits N)+1

theorem profileGrid_pos (N : ℕ) : 0 < profileGrid N := by unfold profileGrid; omega

def angularApprox (q : ℚ) (P : ℕ) : Ball :=
  ⟨(glueApprox (1-(Calibration.cosTurnApprox q 1 (P+4)).center) (P+4)).center,
    (1/2 : ℚ)^P,by positivity⟩

theorem angularApprox_radius (q : ℚ) (P : ℕ) :
    (angularApprox q P).radius=(1/2 : ℚ)^P := rfl

theorem angularApprox_contains (q : ℚ) (P : ℕ) (hq : |q| ≤ 1) :
    (angularApprox q P).Contains (angular (2*Real.pi*(q : ℝ))) := by
  have hc := Calibration.cosTurnApprox_contains q 1 (P+4) (by simpa using hq)
  rw [Ball.Contains, Calibration.cosTurnApprox_radius] at hc
  push_cast at hc
  have ha : |(1-Real.cos (2*Real.pi*(q : ℝ)))-
      ((1-(Calibration.cosTurnApprox q 1 (P+4)).center : ℚ) : ℝ)| ≤ (1/2 : ℝ)^(P+4) := by
    simpa only [Rat.cast_sub, Rat.cast_one, sub_sub_sub_cancel_left, abs_sub_comm] using hc
  have hg := glueApprox_error (1-(Calibration.cosTurnApprox q 1 (P+4)).center) (P+4) ha
  change |expNegInvGlue (1-Real.cos (2*Real.pi*(q : ℝ)))-
    ((glueApprox (1-(Calibration.cosTurnApprox q 1 (P+4)).center) (P+4)).center : ℝ)| ≤ _
  apply hg.trans
  change 2*(1/2 : ℝ)^(P+4)+(1/2 : ℝ)^(P+4) ≤ (((1/2 : ℚ)^P : ℚ) : ℝ)
  push_cast
  rw [pow_add]
  nlinarith only [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) P]

theorem angular_nonneg (φ : ℝ) : 0 ≤ angular φ := expNegInvGlue.nonneg _

theorem angular_le_one (φ : ℝ) : angular φ ≤ 1 := by
  rw [angular_eq_radial]
  exact radial_le_one _

theorem angularApprox_center_bound (q : ℚ) (P : ℕ) (hq : |q| ≤ 1) :
    |(angularApprox q P).center| ≤ 2 := by
  have h := angularApprox_contains q P hq
  rw [Ball.Contains, angularApprox_radius] at h
  push_cast at h
  have he : (1/2 : ℝ)^P ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hb : |((angularApprox q P).center : ℝ)| ≤ 2 := by
    have ht := abs_sub_le ((angularApprox q P).center : ℝ) (angular (2*Real.pi*(q : ℝ))) 0
    simp only [sub_zero, abs_sub_comm _ (angular _), abs_of_nonneg (angular_nonneg _)] at ht
    linarith [angular_le_one (2*Real.pi*(q : ℝ))]
  exact_mod_cast hb

theorem grid_fraction_bound (grid : ℕ) [NeZero grid] (j : ZMod grid) :
    |(j.val : ℚ)/grid| ≤ 1 := by
  have hg : 0 < (grid : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne grid)
  rw [abs_of_nonneg (by positivity : 0 ≤ (j.val : ℚ)/grid)]
  apply (div_le_iff₀ hg).mpr
  simp only [one_mul]
  exact_mod_cast (ZMod.val_lt j).le

#print axioms angularApprox_contains
#print axioms angularApprox_center_bound

end Maxwell.Continuum.Profile
