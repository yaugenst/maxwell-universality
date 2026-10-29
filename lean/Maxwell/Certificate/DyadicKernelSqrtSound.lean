import Maxwell.Certificate.DyadicKernelSqrt
import Maxwell.Certificate.DyadicKernelRoundedSound
import Mathlib.Data.Nat.Sqrt

namespace Maxwell.Certificate.DyadicKernel

theorem centerRadius_contains {lo hi : ℤ} {x : ℝ}
    (hl : (lo:ℝ) ≤ x) (hh : x ≤ (hi:ℝ)) :
    |x-(centerRadius lo hi).1| ≤ ((centerRadius lo hi).2:ℝ) := by
  have h₀ : (centerRadius lo hi).1-((centerRadius lo hi).2:ℤ) ≤ lo := by
    have hh : |(lo+hi)/2-lo| ≤
        ((max ((lo+hi)/2-lo).natAbs (hi-(lo+hi)/2).natAbs:ℕ):ℤ) := by
      simpa only [Int.natCast_natAbs] using
        Int.ofNat_le.mpr (Nat.le_max_left ((lo+hi)/2-lo).natAbs (hi-(lo+hi)/2).natAbs)
    dsimp [centerRadius]
    linarith [le_abs_self ((lo+hi)/2-lo)]
  have h₁ : hi ≤ (centerRadius lo hi).1+((centerRadius lo hi).2:ℤ) := by
    have hh : |hi-(lo+hi)/2| ≤
        ((max ((lo+hi)/2-lo).natAbs (hi-(lo+hi)/2).natAbs:ℕ):ℤ) := by
      simpa only [Int.natCast_natAbs] using
        Int.ofNat_le.mpr (Nat.le_max_right ((lo+hi)/2-lo).natAbs (hi-(lo+hi)/2).natAbs)
    dsimp [centerRadius]
    linarith [le_abs_self (hi-(lo+hi)/2)]
  have h₀' : ((centerRadius lo hi).1:ℝ)-((centerRadius lo hi).2:ℝ) ≤ (lo:ℝ) := by
    exact_mod_cast h₀
  have h₁' : (hi:ℝ) ≤ ((centerRadius lo hi).1:ℝ)+((centerRadius lo hi).2:ℝ) := by
    exact_mod_cast h₁
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem sqrtRound_contains {p : ℕ} {a b : Rectangle} {x : ℝ}
    (h : sqrtRound p a = some b) (ha : a.toDyadic.Contains p (x:ℂ)) :
    b.toDyadic.Contains p (Real.sqrt x:ℂ) := by
  unfold sqrtRound at h
  split at h
  next hp =>
    cases Option.some.inj h
    let s : ℝ := (2:ℝ)^p
    have hs : 0 < s := by positivity
    have hl0 : 0 ≤ (a.re-(a.radius:ℤ))*2^p := mul_nonneg hp (by positivity)
    have hh0 : 0 ≤ (a.re+(a.radius:ℤ))*2^p := by
      apply mul_nonneg _ (by positivity)
      have hr : (0:ℤ) ≤ a.radius := by positivity
      omega
    have helo : ((((a.re-(a.radius:ℤ))*2^p).toNat:ℕ):ℝ) =
        ((a.re:ℝ)-(a.radius:ℝ))*s := by
      rw [← Int.cast_natCast,Int.toNat_of_nonneg hl0]
      push_cast
      rfl
    have hehi : ((((a.re+(a.radius:ℤ))*2^p).toNat:ℕ):ℝ) =
        ((a.re:ℝ)+(a.radius:ℝ))*s := by
      rw [← Int.cast_natCast,Int.toNat_of_nonneg hh0]
      push_cast
      rfl
    have hla := (abs_le.mp ha.1).1
    have hha := (abs_le.mp ha.1).2
    change -(a.radius:ℝ) ≤ x*s-(a.re:ℝ) at hla
    change x*s-(a.re:ℝ) ≤ (a.radius:ℝ) at hha
    have hx : 0 ≤ x := by
      have hpr : (0:ℝ) ≤ (a.re:ℝ)-(a.radius:ℝ) := by exact_mod_cast hp
      exact (mul_nonneg_iff_of_pos_right hs).mp (by linarith)
    have hlo := Nat.sqrt_le' (((a.re-(a.radius:ℤ))*2^p).toNat)
    have hhi := Nat.lt_succ_sqrt' (((a.re+(a.radius:ℤ))*2^p).toNat)
    have hlo' : (Nat.sqrt (((a.re-(a.radius:ℤ))*2^p).toNat):ℝ)^2 ≤
        ((a.re:ℝ)-(a.radius:ℝ))*s := by
      rw [← helo]
      exact_mod_cast hlo
    have hhi' : ((a.re:ℝ)+(a.radius:ℝ))*s <
        (Nat.sqrt (((a.re+(a.radius:ℤ))*2^p).toNat)+1:ℝ)^2 := by
      rw [← hehi]
      exact_mod_cast hhi
    have hsq : (Real.sqrt x*s)^2 = x*s^2 := by rw [mul_pow,Real.sq_sqrt hx]
    have hroot : 0 ≤ Real.sqrt x*s := mul_nonneg (Real.sqrt_nonneg x) hs.le
    constructor
    · change |Real.sqrt x*s-(centerRadius _ _).1| ≤ ((centerRadius _ _).2:ℝ)
      apply centerRadius_contains
      · push_cast
        nlinarith [mul_le_mul_of_nonneg_right (show (a.re:ℝ)-(a.radius:ℝ) ≤ x*s by linarith) hs.le]
      · push_cast
        nlinarith [mul_le_mul_of_nonneg_right (show x*s ≤ (a.re:ℝ)+(a.radius:ℝ) by linarith) hs.le]
    · simp [Rectangle.toDyadic]
  next => contradiction

end Maxwell.Certificate.DyadicKernel
