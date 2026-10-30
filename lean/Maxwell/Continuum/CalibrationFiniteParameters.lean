import Maxwell.Continuum.CalibrationSandwichPrecision
import Maxwell.Continuum.CalibrationPowerStability
import Maxwell.Continuum.CalibrationPeriodizedAuxiliary

/-! Executable integer supercell and precision parameters. The huge
fixed master power is retained symbolically in every proof. -/

namespace Maxwell.Continuum.Calibration

open MasterConstants

attribute [local irreducible] exponent Cs

def supercellSize (L r N ell : ℕ) : ℕ :=
  2*((2 : ℕ)^(4*exponent)*L*(N+ell+2)^2+16*(L+r+1))

theorem supercellSize_even (L r N ell : ℕ) : Even (supercellSize L r N ell) :=
  ⟨(2 : ℕ)^(4*exponent)*L*(N+ell+2)^2+16*(L+r+1),by unfold supercellSize; omega⟩

theorem supercellSize_positive (L r N ell : ℕ) : 0 < supercellSize L r N ell := by
  unfold supercellSize
  omega

theorem supercellSize_real (L r N ell : ℕ) :
    (supercellSize L r N ell : ℝ)=
      2*(Cs^4*(L : ℝ)*((N : ℝ)+(ell : ℝ)+2)^2+16*((L : ℝ)+(r : ℝ)+1)) := by
  unfold supercellSize Cs
  push_cast
  rw [← pow_mul,Nat.mul_comm exponent 4]

theorem supercellSize_geometry (L r N ell : ℕ) :
    16*((L : ℝ)+(r : ℝ)+1) ≤ (supercellSize L r N ell : ℝ) := by
  rw [supercellSize_real]
  have hc : 0 ≤ Cs^4*(L : ℝ)*((N : ℝ)+(ell : ℝ)+2)^2 := by positivity
  have hr : 0 ≤ 16*((L : ℝ)+(r : ℝ)+1) := by positivity
  linarith

theorem supercellSize_accuracy (L r N ell : ℕ) :
    Cs^4*(L : ℝ)*((N : ℝ)+(ell : ℝ)+2)^2 ≤ (supercellSize L r N ell : ℝ) := by
  rw [supercellSize_real]
  have hc : 0 ≤ Cs^4*(L : ℝ)*((N : ℝ)+(ell : ℝ)+2)^2 := by positivity
  have hr : 0 ≤ 16*((L : ℝ)+(r : ℝ)+1) := by positivity
  linarith

def lengthBits (L : ℕ) : ℕ := Nat.clog 2 (L+1)

theorem lengthBits_bound (L : ℕ) : (L : ℝ) ≤ (2 : ℝ)^lengthBits L := by
  have h : L ≤ 2^lengthBits L :=
    (Nat.le_succ L).trans (Nat.le_pow_clog (by decide : 1<2) (L+1))
  exact_mod_cast h

def torusScale (L M : ℕ) : ℚ := 2*(M : ℚ)/(L : ℚ)

theorem torusScale_lower {L M : ℕ} (hL : 0<L)
    (hM : 16*((L : ℝ)+1)≤(M : ℝ)) : 4 ≤ (torusScale L M : ℝ) := by
  have hLr : (0 : ℝ)<L := by exact_mod_cast hL
  simp only [torusScale,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast]
  apply (le_div_iff₀ hLr).mpr
  linarith

theorem torusScale_bound {L M : ℕ} (hL : 0<L) :
    (torusScale L M : ℝ) ≤ (2 : ℝ)^(lengthBits M+1) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  simp only [torusScale,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast]
  calc
    _ ≤ 2*(M : ℝ) := (div_le_self (by positivity) hL1)
    _ ≤ 2*(2 : ℝ)^lengthBits M := mul_le_mul_of_nonneg_left (lengthBits_bound M) (by norm_num)
    _ = _ := by rw [pow_succ]; ring

#print axioms supercellSize_accuracy
#print axioms torusScale_bound

end Maxwell.Continuum.Calibration
