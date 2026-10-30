import Maxwell.Cost.SelectedParameters.GeometricValues
import Maxwell.Continuum.CalibrationElementary

/-! Exact common-denominator evaluation of finite rational Taylor sums.
Both signed parts are stored as natural numbers; the denominator is
b^n n!, so intermediate widths grow polynomially rather than by repeated
unreduced rational addition. -/

namespace Maxwell.Continuum.RationalTaylor
open Maxwell.Cost

inductive Sign where
  | zero | plus | minus
  deriving DecidableEq, Repr

def Sign.positive : Sign → Bool
  | .plus => true
  | _ => false

def Sign.negative : Sign → Bool
  | .minus => true
  | _ => false

def Sign.value : Sign → ℚ
  | .zero => 0
  | .plus => 1
  | .minus => -1

def numerator (a b : ℕ) (keep : ℕ → Bool) : ℕ → ℕ
  | 0 => if keep 0 then 1 else 0
  | n+1 => b*(n+1)*numerator a b keep n + if keep (n+1) then a^(n+1) else 0

def denominator (b n : ℕ) : ℕ := b^n*n.factorial

theorem denominator_pos {b : ℕ} (hb : 0 < b) (n : ℕ) : 0 < denominator b n := by
  unfold denominator
  positivity

theorem denominator_succ (b n : ℕ) : denominator b (n+1) = b*(n+1)*denominator b n := by
  simp only [denominator,pow_succ,Nat.factorial_succ]
  ring

theorem numerator_value (a b : ℕ) (hb : 0 < b) (keep : ℕ → Bool) (n : ℕ) :
    (numerator a b keep n : ℚ)/(denominator b n : ℚ) =
      ∑ k ∈ Finset.range (n+1), if keep k then ((a : ℚ)/b)^k/(k.factorial : ℚ) else 0 := by
  induction n with
  | zero => simp [numerator,denominator]
  | succ n ih =>
    have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hn0 : ((n+1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hD : (denominator b n : ℚ) ≠ 0 := by exact_mod_cast (denominator_pos hb n).ne'
    have hfac : (n.factorial : ℚ) ≠ 0 := by positivity
    rw [Finset.sum_range_succ]
    rw [← ih]
    simp only [numerator,denominator_succ,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
    cases keep (n+1) <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_zero,Nat.cast_pow]
    · field_simp
      ring
    · simp only [denominator,Nat.cast_mul,Nat.cast_pow,Nat.factorial_succ,Nat.cast_add,Nat.cast_one]
      rw [div_pow]
      field_simp
      ring

def value (a b : ℕ) (signs : ℕ → Sign) (n : ℕ) : ℚ :=
  ((numerator a b (fun k => (signs k).positive) n : ℚ)-
    (numerator a b (fun k => (signs k).negative) n : ℚ))/(denominator b n : ℚ)

theorem value_sum (a b : ℕ) (hb : 0 < b) (signs : ℕ → Sign) (n : ℕ) :
    value a b signs n =
      ∑ k ∈ Finset.range (n+1), (signs k).value*((a : ℚ)/b)^k/(k.factorial : ℚ) := by
  unfold value
  rw [sub_div,numerator_value a b hb,numerator_value a b hb,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  cases signs k <;> simp [Sign.positive,Sign.negative,Sign.value]
  all_goals ring

theorem nat_bits_le_self (n : ℕ) : n.bits.length ≤ n := by
  simpa only [WordLength.countBits_eq] using WordLength.countBits_length n

theorem factorial_bits (n : ℕ) : n.factorial.bits.length ≤ n^2+1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ]
    have h := RationalAccumulator.bits_mul_le (n+1) n.factorial
    have hn := nat_bits_le_self (n+1)
    nlinarith only [h,hn,ih]

def width (N W : ℕ) : ℕ := (N+1)*(W+N+3)

theorem numerator_bits (a b : ℕ) (keep : ℕ → Bool) (N W : ℕ)
    (ha : a.bits.length ≤ W) (hb : b.bits.length ≤ W) (n : ℕ) (hn : n ≤ N) :
    (numerator a b keep n).bits.length ≤ (n+1)*(W+N+3) := by
  induction n with
  | zero => cases h : keep 0 <;> simp [numerator,h]
  | succ n ih =>
    have hi := ih (by omega)
    have hfactor := (RationalAccumulator.bits_mul_le b (n+1)).trans
      (Nat.add_le_add hb ((nat_bits_le_self (n+1)).trans hn))
    have hprod := (RationalAccumulator.bits_mul_le (b*(n+1)) (numerator a b keep n)).trans
      (Nat.add_le_add hfactor hi)
    have hpower := (SelectedParameters.Geometric.power_bits a (n+1)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left (n+1) ha) 1)
    simp only [numerator]
    cases keep (n+1) <;> simp only [Bool.false_eq_true,ite_false,ite_true,add_zero]
    · nlinarith only [hprod]
    · have hs := RationalAccumulator.bits_add_le (b*(n+1)*numerator a b keep n) (a^(n+1))
      have hmax := max_le (show (b*(n+1)*numerator a b keep n).bits.length ≤
          (W+N)+(n+1)*(W+N+3) from hprod)
        (show (a^(n+1)).bits.length ≤ (W+N)+(n+1)*(W+N+3) by nlinarith only [hpower])
      nlinarith only [hs,hmax]

theorem denominator_bits (b n N W : ℕ) (hn : n ≤ N) (hb : b.bits.length ≤ W) :
    (denominator b n).bits.length ≤ width N W := by
  have hp := (SelectedParameters.Geometric.power_bits b n).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left n hb) 1)
  have hf := factorial_bits n
  have hm := RationalAccumulator.bits_mul_le (b^n) n.factorial
  have hnN := Nat.mul_le_mul_left n hn
  have hnW := Nat.mul_le_mul_right W hn
  change (b^n*n.factorial).bits.length ≤ _
  unfold width
  nlinarith only [hp,hf,hm,hnN,hnW,hn]

#print axioms value_sum
#print axioms numerator_bits
#print axioms denominator_bits

end Maxwell.Continuum.RationalTaylor
