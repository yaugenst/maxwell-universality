import Maxwell.Continuum.RationalChebyshevTable
import Mathlib.Data.Nat.Size

/-! Linear bit widths for the executable two-row Chebyshev recurrence. -/

namespace Maxwell.Continuum.Calibration

theorem chebyshevState_abs (W n : ℕ) :
    (∀ i : Fin W, |(chebyshevState W n).1.get i|≤(3 : ℤ)^n) ∧
    (∀ i : Fin W, |(chebyshevState W n).2.get i|≤(3 : ℤ)^(n+1)) := by
  induction n with
  | zero =>
    constructor <;> intro i <;> simp only [chebyshevState,vector_get_ofFn]
    · split_ifs <;> norm_num
    · split_ifs <;> norm_num
  | succ n ih =>
    refine ⟨ih.2,?_⟩
    intro i
    simp only [chebyshevState,vector_get_ofFn]
    have hb : |(if hi : i.val=0 then 0 else (chebyshevState W n).2.get ⟨i.val-1,by omega⟩)|≤
        (3 : ℤ)^(n+1) := by
      split_ifs
      · positivity
      · exact ih.2 _
    calc
      _ ≤ |2*(if hi : i.val=0 then 0 else (chebyshevState W n).2.get ⟨i.val-1,by omega⟩)|+
          |(chebyshevState W n).1.get i| := abs_sub _ _
      _ ≤ 2*(3 : ℤ)^(n+1)+(3 : ℤ)^n := by
        rw [abs_mul,show |(2 : ℤ)|=2 by norm_num]
        exact add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num)) (ih.1 i)
      _ ≤ (3 : ℤ)^(n+1+1) := by
        simp only [pow_succ]
        nlinarith only [pow_nonneg (by norm_num : (0 : ℤ)≤3) n]

theorem chebyshevRow_abs (W n : ℕ) (i : Fin W) :
    |(chebyshevRow W n).get i|≤(3 : ℤ)^n := (chebyshevState_abs W n).1 i

theorem chebyshevRow_natAbs (W n : ℕ) (i : Fin W) :
    ((chebyshevRow W n).get i).natAbs≤2^(2*n) := by
  have h := chebyshevRow_abs W n i
  rw [← Int.natCast_natAbs] at h
  have hn : ((chebyshevRow W n).get i).natAbs≤3^n := by exact_mod_cast h
  apply hn.trans
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by norm_num : 3≤2^2) n

#print axioms chebyshevRow_natAbs

end Maxwell.Continuum.Calibration
