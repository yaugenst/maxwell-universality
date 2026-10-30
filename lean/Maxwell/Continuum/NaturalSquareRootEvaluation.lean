import Maxwell.Certificate.Interval
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! A literal integer-square-root enclosure with a dyadic denominator. -/

namespace Maxwell.Continuum.Calibration

open Maxwell.Certificate

def sqrtNaturalWord (n N : ℕ) : ℕ := Nat.sqrt (n*2^(2*N))
def sqrtNaturalCenter (n N : ℕ) : ℚ := (sqrtNaturalWord n N : ℚ)/2^N
def sqrtNaturalApprox (n N : ℕ) : Ball := ⟨sqrtNaturalCenter n N,(1/2)^N,by positivity⟩

theorem sqrtNatural_bracket (n N : ℕ) :
    (sqrtNaturalCenter n N : ℝ)≤Real.sqrt n ∧
      Real.sqrt n<(sqrtNaturalCenter n N : ℝ)+(1/2 : ℝ)^N := by
  have hp : (0 : ℝ)<(2 : ℝ)^N := by positivity
  have hlo : (sqrtNaturalWord n N : ℝ)^2≤(n : ℝ)*(2 : ℝ)^(2*N) := by
    exact_mod_cast Nat.sqrt_le' (n*2^(2*N))
  have hhi : (n : ℝ)*(2 : ℝ)^(2*N)<((sqrtNaturalWord n N : ℝ)+1)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' (n*2^(2*N))
  have hs : (Real.sqrt n*(2 : ℝ)^N)^2=(n : ℝ)*(2 : ℝ)^(2*N) := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),← pow_mul]
    congr 2
    omega
  have hk : (sqrtNaturalWord n N : ℝ)≤Real.sqrt n*(2 : ℝ)^N := by
    apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mp
    rwa [hs]
  have hk' : Real.sqrt n*(2 : ℝ)^N<(sqrtNaturalWord n N : ℝ)+1 := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rwa [hs]
  have he : (1/2 : ℝ)^N=1/(2 : ℝ)^N := by rw [div_pow,one_pow]
  simp only [sqrtNaturalCenter,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat]
  constructor
  · exact (div_le_iff₀ hp).mpr hk
  · rw [he,← add_div]
    exact (lt_div_iff₀ hp).mpr hk'

theorem sqrtNaturalApprox_contains (n N : ℕ) : (sqrtNaturalApprox n N).Contains (Real.sqrt n) := by
  have h := sqrtNatural_bracket n N
  change |Real.sqrt n-(sqrtNaturalCenter n N : ℝ)|≤(((1/2 : ℚ)^N : ℚ) : ℝ)
  rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
  push_cast
  linarith [h.2]

theorem sqrtNaturalWord_bound (n N : ℕ) : sqrtNaturalWord n N≤(n+1)*2^N := by
  apply (Nat.sqrt_lt').mpr ?_ |>.le
  have hn : n<(n+1)^2 := by nlinarith
  have hp : 0<2^(2*N) := by positivity
  calc
    _ < (n+1)^2*2^(2*N) := Nat.mul_lt_mul_of_pos_right hn hp
    _ = _ := by rw [mul_pow,← pow_mul]; congr 2; omega

#print axioms sqrtNaturalApprox_contains

end Maxwell.Continuum.Calibration
