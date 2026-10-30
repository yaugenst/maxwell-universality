import Maxwell.Continuum.CalibrationNeumannRawTable
import Maxwell.Cost.CalibrationMatrix.PowerSemantics

/-! Fixed-denominator powers for the finite calibration operator.  The
independently stored sign channels are bounded before cancellation. -/

namespace Maxwell.Continuum.Calibration.PowerMachine

open Maxwell.Cost Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
open NeumannMachine
open scoped BigOperators
set_option maxHeartbeats 2000000

def rationalPower {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    ℕ → Fin n → ℚ
  | 0 => b
  | k+1 => A.mulVec (rationalPower A b k)

theorem matrixPower_bound {n : ℕ} {A : ChannelMatrix n} {a b : ℕ}
    (hA : A.Bounded a) (x : Channels n) (hx : x.Bounded b) (k : ℕ) :
    (matrixPower A x k).Bounded (b*(2*n*a)^k) := by
  induction k with
  | zero => simpa only [matrixPower,pow_zero,Nat.mul_one] using hx
  | succ k ih =>
    simpa only [matrixPower,pow_succ,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
      using matvec_bound hA ih

/-- One common denominator, including the initial vector, is retained
through every matrix power. -/
theorem rawTable_power {n : ℕ} (a : CoefficientIndex n → Parts)
    (ha : ∀ i, (a i).Valid) (k : ℕ) (i : Fin n) :
    ((matrixPower (rawMatrix a) (rawSource a) k).value i : ℚ)/
        (SharedTable.denominator a : ℚ)^(k+1) =
      rationalPower (fun i j => (a (.inr (i,j))).value)
        (fun i => (a (.inl i)).value) k i := by
  have hD : (SharedTable.denominator a : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (SharedTable.denominator_pos a ha).ne'
  have source (i : Fin n) :
      ((rawSource a).value i : ℚ)/(SharedTable.denominator a : ℚ) = (a (.inl i)).value :=
    SharedTable.integerValue_sound a ha (.inl i)
  have matrix (i j : Fin n) :
      ((rawMatrix a).value i j : ℚ)/(SharedTable.denominator a : ℚ) =
        (a (.inr (i,j))).value :=
    SharedTable.integerValue_sound a ha (.inr (i,j))
  induction k generalizing i with
  | zero => simpa only [matrixPower,rationalPower,Nat.zero_add,pow_one] using source i
  | succ k ih =>
    simp only [matrixPower,value_matvec,Int.cast_sum,Int.cast_mul,rationalPower,
      Matrix.mulVec,dotProduct,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (((rawMatrix a).value i j : ℚ)/(SharedTable.denominator a : ℚ))*
          (((matrixPower (rawMatrix a) (rawSource a) k).value j : ℚ)/
            (SharedTable.denominator a : ℚ)^(k+1)) := by
        rw [pow_succ]
        field_simp
      _ = _ := by rw [matrix,ih]

def coefficientBits (n W : ℕ) : ℕ := (n+n*n+1)*(W+1)

/-- Linear in the iteration count, including unreduced positive and
negative channels. -/
def rawPowerWidth (n W N : ℕ) : ℕ :=
  coefficientBits n W+1+(n.size+coefficientBits n W+2)*N

theorem growth_size (n W : ℕ) :
    (2*n*rawCoefficientBound n W).size ≤ n.size+coefficientBits n W+2 := by
  have h : 2*n*rawCoefficientBound n W ≤ 2^(1+n.size+coefficientBits n W) := by
    calc
      _ ≤ 2*2^n.size*2^(coefficientBits n W) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (Nat.lt_size_self n).le)
      _ = _ := by rw [pow_add,pow_add,pow_one]
  have hs := Nat.size_le_size h
  simp only [Nat.size_pow] at hs
  omega

theorem rawTable_power_width {n : ℕ} (a : CoefficientIndex n → Parts) (W N : ℕ)
    (ha : ∀ i, (a i).Width W) (k : ℕ) (hk : k ≤ N) (i : Fin n) :
    ((matrixPower (rawMatrix a) (rawSource a) k).positive i).bits.length ≤ rawPowerWidth n W N ∧
    ((matrixPower (rawMatrix a) (rawSource a) k).negative i).bits.length ≤ rawPowerWidth n W N := by
  have h := (matrixPower_bound (rawMatrix_bounded a W ha) (rawSource a)
    (rawSource_bounded a W ha) k).bit_bound i
  have hg := growth_size n W
  have hs : (rawCoefficientBound n W).size = coefficientBits n W+1 := by
    simp only [rawCoefficientBound,coefficientBits,Nat.size_pow]
  rw [hs] at h
  have hm := Nat.mul_le_mul hg hk
  exact ⟨by simpa only [← Nat.size_eq_bits_len,rawPowerWidth] using h.1.trans (Nat.add_le_add_left hm _),
    by simpa only [← Nat.size_eq_bits_len,rawPowerWidth] using h.2.trans (Nat.add_le_add_left hm _)⟩

theorem rawTable_denominator_width {n : ℕ} (a : CoefficientIndex n → Parts) (W N : ℕ)
    (ha : ∀ i, (a i).Width W) :
    ((SharedTable.denominator a)^(N+1)).bits.length ≤
      ((n+n*n)*W+1)*(N+1) := by
  have hD := SharedTable.denominator_bound a W ha
  rw [coefficientIndex_card] at hD
  have hs : (SharedTable.denominator a).size ≤ (n+n*n)*W+1 := by
    simpa only [Nat.size_pow] using Nat.size_le_size hD
  have hdirect : ((SharedTable.denominator a)^(N+1)).size ≤
      (SharedTable.denominator a).size*(N+1) := by
    apply Nat.size_le.mpr
    have hd := Nat.pow_lt_pow_left (Nat.lt_size_self (SharedTable.denominator a)) (by omega : N+1 ≠ 0)
    simpa only [← pow_mul] using hd
  simpa only [← Nat.size_eq_bits_len] using hdirect.trans (Nat.mul_le_mul_right _ hs)

#print axioms rawTable_power
#print axioms rawTable_power_width
#print axioms rawTable_denominator_width

end Maxwell.Continuum.Calibration.PowerMachine
