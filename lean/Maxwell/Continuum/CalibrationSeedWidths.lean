import Maxwell.Continuum.CalibrationSeed
import Maxwell.Continuum.RationalSquareRootWidths

/-! Literal reduced-rational widths of the executable 24-coordinate
corner seed. Guard bits and normalization retain linear precision. -/

namespace Maxwell.Continuum.Calibration

open RationalWords

theorem seedRadical_width (N : ℕ) : Width (seedRadical N) (N+29) := by
  simpa only [seedRadical, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    sqrtNaturalCenter_width 19 (N+7)

theorem seedRaw_width (N : ℕ) (j : Fin 3) : Width (seedRaw N j) (N+64) := by
  have h := seedRadical_width N
  have h8 : Width 8 4 := by constructor <;> decide
  have h15 : Width 15 4 := by constructor <;> decide
  have h6 : Width 6 3 := by constructor <;> decide
  have h7 : Width 7 3 := by constructor <;> decide
  have h10 : Width 10 4 := by constructor <;> decide
  fin_cases j
  · change Width ((8+seedRadical N)*15⁻¹) _
    exact ((h8.add h).mul (h15.inv (by norm_num))).mono (by omega)
  · change Width ((1-seedRadical N)*6⁻¹) _
    exact ((width_one.sub h).mul (h6.inv (by norm_num))).mono (by omega)
  · change Width ((seedRadical N-7)*10⁻¹) _
    exact ((h.sub h7).mul (h10.inv (by norm_num))).mono (by omega)

theorem seedDenominatorSq_width (N : ℕ) : Width (seedDenominatorSq N) (N+64) := by
  have h := seedRadical_width N
  have h8 : Width 8 4 := by constructor <;> decide
  have h28 : Width 28 5 := by constructor <;> decide
  have h361 : Width 361 9 := by constructor <;> decide
  have h225 : Width 225 8 := by constructor <;> decide
  change Width ((8*(361-28*seedRadical N))*225⁻¹) _
  exact ((h8.mul (h361.sub (h28.mul h))).mul (h225.inv (by norm_num))).mono (by omega)

theorem seedDenominator_width (N : ℕ) : Width (seedDenominator N) (4*(N+64)) := by
  exact (sqrtRationalCenter_width (seedDenominatorSq_width N) (N+7)).mono (by omega)

theorem seedComponent_width (N : ℕ) (j : Fin 3) : Width (seedComponent N j) (5*(N+64)) := by
  have hn : seedDenominator N ≠ 0 := by
    intro h
    have ht := seedDenominator_lower N
    rw [h, Rat.cast_zero] at ht
    norm_num at ht
  change Width (seedRaw N j*(seedDenominator N)⁻¹) _
  exact ((seedRaw_width N j).mul ((seedDenominator_width N).inv hn)).mono (by omega)

theorem seedSign_width (s : Corner.Parity) (j : Fin 3) : Width (seedSign s j) 1 := by
  obtain ⟨a,b,c⟩ := s
  cases a <;> cases b <;> cases c <;> fin_cases j <;> norm_num only [seedSign,
    Bool.false_eq_true, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    mul_one, one_mul, neg_mul_neg, neg_one_mul, mul_neg_one, neg_neg] <;>
    first | exact width_one | exact width_one.neg

theorem rationalSeedCoordinates_width (N : ℕ) (i : Fin 24) :
    Width (rationalSeedCoordinates N i).1 (6*(N+64)) ∧
    Width (rationalSeedCoordinates N i).2 (6*(N+64)) := by
  constructor
  · exact ((seedSign_width _ _).mul (seedComponent_width N _)).mono (by omega)
  · exact width_zero'.mono (by omega)

theorem rationalSeed_width (N : ℕ) (ν : FreeFiber.Alias) (j : Fin 3) :
    Width (rationalSeed N ν j).1 (6*(N+64)) ∧
    Width (rationalSeed N ν j).2 (6*(N+64)) := by
  unfold rationalSeed rationalExpandCoordinates
  split_ifs
  · exact rationalSeedCoordinates_width N _
  · exact ⟨width_zero'.mono (by omega), width_zero'.mono (by omega)⟩

#print axioms rationalSeedCoordinates_width
#print axioms rationalSeed_width

end Maxwell.Continuum.Calibration
