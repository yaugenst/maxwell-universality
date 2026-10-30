import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Rat.Cast.Lemmas

/-! Executable materialized coefficient tables for Chebyshev polynomials. -/

namespace Maxwell.Continuum.Calibration

open Polynomial

theorem vector_get_ofFn {α : Type*} {W : ℕ} (f : Fin W → α) (i : Fin W) :
    (Vector.ofFn f).get i=f i := by simp [Vector.get,Fin.cast]

def chebyshevState (W : ℕ) : ℕ → Vector ℤ W × Vector ℤ W
  | 0 => (Vector.ofFn (fun i => if i.val=0 then 1 else 0),
      Vector.ofFn (fun i => if i.val=1 then 1 else 0))
  | n+1 =>
      let v := chebyshevState W n
      (v.2, Vector.ofFn (fun i =>
        2*(if hi : i.val=0 then 0 else v.2.get ⟨i.val-1,by omega⟩)-v.1.get i))

theorem chebyshevState_coeff (W n : ℕ) :
    (∀ i : Fin W, (chebyshevState W n).1.get i=(Chebyshev.T ℤ (n : ℤ)).coeff i) ∧
    (∀ i : Fin W, (chebyshevState W n).2.get i=(Chebyshev.T ℤ ((n : ℤ)+1)).coeff i) := by
  induction n with
  | zero =>
    constructor <;> intro i <;> simp [chebyshevState,vector_get_ofFn,coeff_one,coeff_X,eq_comm]
  | succ n ih =>
    constructor
    · intro i
      simpa only [chebyshevState,Nat.cast_add,Nat.cast_one] using ih.2 i
    · intro i
      simp only [chebyshevState,vector_get_ofFn]
      rw [show ((n+1 : ℕ) : ℤ)+1=(n : ℤ)+2 by omega,Chebyshev.T_add_two,
        coeff_sub,mul_assoc,coeff_ofNat_mul,ih.1 i]
      by_cases hi : i.val=0
      · simp only [hi,↓reduceDIte,coeff_X_mul_zero]
      · simp only [hi,↓reduceDIte]
        rw [ih.2]
        congr 2
        have he : i.val=(i.val-1)+1 := by omega
        conv_rhs => rw [he,coeff_X_mul]

def chebyshevRow (W n : ℕ) : Vector ℤ W := (chebyshevState W n).1

theorem chebyshevRow_coeff (W n : ℕ) (i : Fin W) :
    (chebyshevRow W n).get i=(Chebyshev.T ℤ (n : ℤ)).coeff i := (chebyshevState_coeff W n).1 i

theorem chebyshevRow_polynomial (n : ℕ) :
    Polynomial.ofFn (n+1) (chebyshevRow (n+1) n).get=Chebyshev.T ℤ (n : ℤ) := by
  apply Polynomial.ext
  intro k
  by_cases hk : k<n+1
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hk,chebyshevRow_coeff]
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [Chebyshev.natDegree_T,Int.natAbs_natCast]
    omega

theorem chebyshevRow_coeff_rat (W n : ℕ) (i : Fin W) :
    ((chebyshevRow W n).get i : ℚ)=(Chebyshev.T ℚ (n : ℤ)).coeff i := by
  rw [chebyshevRow_coeff,← Chebyshev.map_T (Int.castRingHom ℚ) (n : ℤ),coeff_map]
  rfl

#print axioms chebyshevRow_coeff
#print axioms chebyshevRow_polynomial

end Maxwell.Continuum.Calibration
