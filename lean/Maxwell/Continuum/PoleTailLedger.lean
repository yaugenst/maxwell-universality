import Maxwell.Continuum.PoleTailBounds
import Maxwell.Continuum.MasterConstants
import Mathlib.Data.Nat.Choose.Bounds

/-! Symbolic arithmetic for the uniform sixteenth-order cutoff tail. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.OscillatoryPole

open PeriodicBand

theorem poleTail_factorial {n : ℕ} (hn : n ≤ 16) :
    (n.factorial : ℝ) ≤ (2 : ℝ)^64 := by
  calc
    _ ≤ ((16 : ℕ).factorial : ℝ) := by exact_mod_cast Nat.factorial_le hn
    _ ≤ (16 : ℝ)^16 := by exact_mod_cast Nat.factorial_le_pow 16
    _ = _ := by rw [show (16 : ℝ)=2^4 by norm_num, ← pow_mul]

theorem poleTail_cutoff_powers :
    2/poleLongitudinalScale = (2 : ℝ)^2049 ∧
      8/poleLongitudinalScale^2 = (2 : ℝ)^4099 ∧
      800/poleLongitudinalScale ≤ (2 : ℝ)^2058 := by
  unfold poleLongitudinalScale
  constructor
  · rw [div_inv_eq_mul, pow_succ (2 : ℝ) 2048]
    exact mul_comm _ _
  constructor
  · rw [inv_pow, div_inv_eq_mul, ← pow_mul,
      show (8 : ℝ)=2^3 by norm_num, ← pow_add]
  · rw [div_inv_eq_mul, show 2058=10+2048 by omega, pow_add]
    exact mul_le_mul_of_nonneg_right (by norm_num : (800 : ℝ)≤2^10) (by positivity)

theorem poleTail_term_ledger {n k : ℕ} (hn : n ≤ 16) (hk : k ≤ n) :
    tailTermBound poleLongitudinalScale n k ≤ (2 : ℝ)^67976 := by
  have ha := poleCutoff_scales.1
  have hf := poleTail_factorial hn
  have hfk := poleTail_factorial (hk.trans hn)
  have hfn := poleTail_factorial ((Nat.sub_le n k).trans hn)
  have hp (m : ℕ) (hm : m ≤ 17) :
      (2/poleLongitudinalScale)^m ≤ (2 : ℝ)^34833 := by
    rw [poleTail_cutoff_powers.1, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hpn : (2/poleLongitudinalScale)^(n-1) ≤ (2 : ℝ)^32784 := by
    rw [poleTail_cutoff_powers.1, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hcut : (800/poleLongitudinalScale)^k ≤ (2 : ℝ)^32928 := by
    calc
      _ ≤ ((2 : ℝ)^2058)^k := pow_le_pow_left₀ (by positivity) poleTail_cutoff_powers.2.2 _
      _ = (2 : ℝ)^(2058*k) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  by_cases hz : k = 0
  · rw [tailTermBound, ite_eq_left hz, poleTail_cutoff_powers.2.1]
    calc
      _ ≤ (2 : ℝ)^64*2^32784*2^4099 := by gcongr
      _ = (2 : ℝ)^36947 := by rw [← pow_add, ← pow_add]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by norm_num)
  · have hc : (n.choose k : ℝ) ≤ (2 : ℝ)^16 := by
      calc
        _ ≤ (2 : ℝ)^n := by exact_mod_cast Nat.choose_le_two_pow n k
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) hn
    rw [tailTermBound, ite_eq_right hz]
    calc
      _ ≤ (2 : ℝ)^16*(2^7*2^32928*(2^64)^2)*2^64*2^34833 := by
        gcongr
        · norm_num
        · exact hp _ (by omega)
      _ = _ := by simp only [← pow_mul, ← pow_add]

theorem poleTail_derivative_ledger {n : ℕ} (hn : n ≤ 16) :
    tailDerivativeBound poleLongitudinalScale n ≤ (2 : ℝ)^70000 := by
  unfold tailDerivativeBound
  calc
    _ ≤ ∑ _k ∈ Finset.range (n+1), (2 : ℝ)^67976 :=
      Finset.sum_le_sum (fun k hk => poleTail_term_ledger hn (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    _ = (n+1 : ℝ)*2^67976 := by simp
    _ ≤ 2^5*2^67976 := mul_le_mul_of_nonneg_right (by exact_mod_cast (show n+1≤2^5 by omega)) (by positivity)
    _ = (2 : ℝ)^67981 := by rw [← pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by norm_num)

theorem poleTail_l1_ledger {n : ℕ} (hn : n ≤ 16) :
    tailDerivativeBound poleLongitudinalScale n*Real.pi ≤ (2 : ℝ)^70002 := by
  calc
    _ ≤ (2 : ℝ)^70000*2^2 := mul_le_mul (poleTail_derivative_ledger hn)
      (by simpa only [show (2 : ℝ)^2 = 4 by norm_num] using Real.pi_lt_four.le) Real.pi_pos.le (by positivity)
    _ = _ := by rw [← pow_add]

theorem poleTail_ledger_master : (2 : ℝ)^70002 ≤ MasterConstants.Cs :=
  MasterConstants.fixed_power_le_Cs (by norm_num [MasterConstants.exponent])

#print axioms poleTail_l1_ledger

end Maxwell.Continuum.OscillatoryPole
