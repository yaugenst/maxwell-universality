import Maxwell.Continuum.CalibrationRationalNeumann
import Mathlib.Data.Rat.Lemmas

/-! A common denominator is formed once from a finite rational coefficient
table. Integer recurrence layers then use successive powers of that one
denominator, rather than multiplying denominators at every stencil sum. -/

namespace Maxwell.Continuum.Calibration

section Denominator

variable {ι : Type*} [Fintype ι]

def commonDenominator (a : ι → ℚ) : ℕ := ∏ i, (a i).den

theorem commonDenominator_pos (a : ι → ℚ) : 0 < commonDenominator a :=
  Finset.prod_pos (fun i _ => (a i).den_pos)

theorem denominator_dvd_common (a : ι → ℚ) (i : ι) : (a i).den ∣ commonDenominator a :=
  Finset.dvd_prod_of_mem (fun j => (a j).den) (Finset.mem_univ i)

def commonNumerator (a : ι → ℚ) (i : ι) : ℤ :=
  (a i).num * ((commonDenominator a/(a i).den : ℕ) : ℤ)

theorem commonNumerator_sound (a : ι → ℚ) (i : ι) :
    (commonNumerator a i : ℚ)/(commonDenominator a : ℚ) = a i := by
  have hd : (commonDenominator a : ℚ) ≠ 0 := by exact_mod_cast (commonDenominator_pos a).ne'
  have hq : ((commonDenominator a/(a i).den : ℕ) : ℚ)*(a i).den = commonDenominator a := by
    exact_mod_cast Nat.div_mul_cancel (denominator_dvd_common a i)
  have hden : ((a i).den : ℚ) ≠ 0 := by exact_mod_cast (a i).den_ne_zero
  have hnum : ((a i).num : ℚ) = a i*(a i).den := (div_eq_iff hden).mp (Rat.num_div_den (a i))
  unfold commonNumerator
  rw [Int.cast_mul, Int.cast_natCast, div_eq_iff hd]
  rw [hnum, mul_assoc, mul_comm ((a i).den : ℚ), hq]

theorem commonDenominator_le_pow (a : ι → ℚ) (W : ℕ)
    (ha : ∀ i, (a i).den ≤ 2^W) : commonDenominator a ≤ 2^(Fintype.card ι*W) := by
  calc
    _ ≤ ∏ _i : ι, 2^W := Finset.prod_le_prod (fun i _ => ha i)
    _ = 2^(Fintype.card ι*W) := by simp only [Finset.prod_const, Finset.card_univ, ← pow_mul]; rw [Nat.mul_comm]

theorem commonNumerator_natAbs_le (a : ι → ℚ) (i : ι) :
    (commonNumerator a i).natAbs ≤ (a i).num.natAbs*commonDenominator a := by
  simp only [commonNumerator, Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)

end Denominator

section Recurrence

variable {ι : Type*} [Fintype ι]

def sharedNumerator (D : ℕ) (A : ι → ι → ℤ) (b : ι → ℤ) : ℕ → ι → ℤ
  | 0 => 0
  | K+1 => fun i => (D : ℤ)^K*b i+∑ j, A i j*sharedNumerator D A b K j

def sharedRationalIteration (D : ℕ) (A : ι → ι → ℤ) (b : ι → ℤ) : ℕ → ι → ℚ
  | 0 => 0
  | K+1 => fun i => (b i : ℚ)/D+∑ j, ((A i j : ℚ)/D)*sharedRationalIteration D A b K j

theorem sharedNumerator_sound (D : ℕ) (hD : 0 < D) (A : ι → ι → ℤ) (b : ι → ℤ) (K : ℕ) (i : ι) :
    (sharedNumerator D A b K i : ℚ)/(D : ℚ)^K = sharedRationalIteration D A b K i := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  induction K generalizing i with
  | zero => simp only [sharedNumerator, sharedRationalIteration, Pi.zero_apply, Int.cast_zero, zero_div]
  | succ K ih =>
    simp only [sharedNumerator, sharedRationalIteration, Int.cast_add, Int.cast_mul,
      Int.cast_pow, Int.cast_natCast, Int.cast_sum]
    simp_rw [← ih, div_mul_div_comm]
    rw [← Finset.sum_div]
    simp only [pow_succ]
    field_simp

#print axioms sharedNumerator_sound

end Recurrence

end Maxwell.Continuum.Calibration
