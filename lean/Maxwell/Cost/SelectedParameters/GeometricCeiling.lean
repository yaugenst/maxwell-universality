import Maxwell.Cost.SelectedParameters.Geometric
import Mathlib.Data.Nat.Log

/-! The existing rational least-power machine computes integer logarithmic
ceilings exactly. No second search program is needed. -/

namespace Maxwell.Cost.SelectedParameters.Geometric

theorem reciprocal_test (b M n : ℕ) (hb : 0<b) (hM : 0<M) :
    (1/(b:ℚ))^n≤1/(M:ℚ) ↔ M≤b^n := by
  have hbq : (0:ℚ)<b := by exact_mod_cast hb
  have hMq : (0:ℚ)<M := by exact_mod_cast hM
  rw [one_div,inv_pow,one_div,inv_le_inv₀ (pow_pos hbq n) hMq]
  exact_mod_cast (Iff.rfl : M≤b^n ↔ M≤b^n)

theorem exponent_eq_clog (b M : ℕ) (hb : 1<b) (hM : 0<M) :
    exponent 1 b 1 M (by decide) hb (by decide) hM=Nat.clog b M := by
  have hp := Realization.geometricSteps_spec ((1:ℚ)/b) ((1:ℚ)/M)
    (div_pos (by norm_num) (by exact_mod_cast (show 0<b by omega)))
    ((div_lt_one (by exact_mod_cast (show 0<b by omega))).mpr (by exact_mod_cast hb))
    (div_pos (by norm_num) (by exact_mod_cast hM))
  apply le_antisymm
  · unfold exponent Realization.geometricSteps
    apply Nat.find_min'
    exact (reciprocal_test b M (Nat.clog b M) (by omega) hM).mpr (Nat.le_pow_clog hb M)
  · exact Nat.clog_le_of_le_pow ((reciprocal_test b M _ (by omega) hM).mp hp)

#print axioms exponent_eq_clog

end Maxwell.Cost.SelectedParameters.Geometric
