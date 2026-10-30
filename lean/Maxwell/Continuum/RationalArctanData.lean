import Maxwell.Continuum.RationalTaylorCenters
import Maxwell.Continuum.CalibrationPi

/-! Polynomial-width exact integer data for the literal Machin series. -/

namespace Maxwell.Continuum.RationalArctan
open Maxwell.Cost RationalTaylor
set_option maxHeartbeats 1000000

def termDenominator (b n : ℕ) : ℕ := b^(2*n+1)*(2*n+1)

def denominator (b : ℕ) : ℕ→ℕ
  | 0 => 1
  | n+1 => termDenominator b n*denominator b n

def numerator (a b : ℕ) (keep : ℕ→Bool) : ℕ→ℕ
  | 0 => 0
  | n+1 => termDenominator b n*numerator a b keep n+
      if keep n then a^(2*n+1)*denominator b n else 0

def value (a b : ℕ) (signs : ℕ→Sign) (n : ℕ) : ℚ :=
  ((numerator a b (fun k => (signs k).positive) n:ℚ)-
    numerator a b (fun k => (signs k).negative) n)/(denominator b n:ℚ)

theorem termDenominator_pos {b : ℕ} (hb : 0<b) (n : ℕ) : 0<termDenominator b n := by
  unfold termDenominator
  positivity

theorem denominator_pos {b : ℕ} (hb : 0<b) (n : ℕ) : 0<denominator b n := by
  induction n with
  | zero => simp [denominator]
  | succ n ih => exact Nat.mul_pos (termDenominator_pos hb n) ih

theorem numerator_value (a b : ℕ) (hb : 0<b) (keep : ℕ→Bool) (n : ℕ) :
    (numerator a b keep n:ℚ)/(denominator b n:ℚ)=
      ∑ k ∈ Finset.range n, if keep k then ((a:ℚ)/b)^(2*k+1)/(2*k+1:ℕ) else 0 := by
  induction n with
  | zero => simp [numerator,denominator]
  | succ n ih =>
    have hb0 : (b:ℚ)≠0 := by exact_mod_cast hb.ne'
    have hn0 : ((2*n+1:ℕ):ℚ)≠0 := by positivity
    have hD : (denominator b n:ℚ)≠0 := by exact_mod_cast (denominator_pos hb n).ne'
    rw [Finset.sum_range_succ,← ih]
    simp only [numerator,denominator,termDenominator,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
    cases keep n <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_zero,Nat.cast_mul,Nat.cast_pow]
    · field_simp
      ring
    · rw [div_pow]
      field_simp

theorem value_sum (a b : ℕ) (hb : 0<b) (signs : ℕ→Sign) (n : ℕ) :
    value a b signs n=
      ∑ k ∈ Finset.range n, (signs k).value*((a:ℚ)/b)^(2*k+1)/(2*k+1:ℕ) := by
  unfold value
  rw [sub_div,numerator_value a b hb,numerator_value a b hb,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  cases signs k <;> simp [Sign.positive,Sign.negative,Sign.value]
  all_goals ring

theorem arctanTaylor_eq (a b : ℕ) (hb : 0<b) (n : ℕ) :
    Maxwell.Certificate.Elementary.arctanTaylor ((a:ℚ)/b) n=value a b negativeSigns n := by
  rw [value_sum a b hb]
  simp only [Maxwell.Certificate.Elementary.arctanTaylor,negativeSigns_value]

def termWidth (N W : ℕ) : ℕ := (2*N+2)*(W+1)+2
def width (N W : ℕ) : ℕ := (N+1)*(termWidth N W+2)

theorem power_bits (a n N W : ℕ) (hn : n≤N) (ha : a.bits.length≤W) :
    (a^(2*n+1)).bits.length≤termWidth N W := by
  have h := (SelectedParameters.Geometric.power_bits a (2*n+1)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul (by omega : 2*n+1≤2*N+1) ha) 1)
  unfold termWidth
  nlinarith only [h]

theorem termDenominator_bits (b n N W : ℕ) (hn : n≤N) (hb : b.bits.length≤W) :
    (termDenominator b n).bits.length≤termWidth N W := by
  have hpow := (SelectedParameters.Geometric.power_bits b (2*n+1)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul (by omega : 2*n+1≤2*N+1) hb) 1)
  have hn' := (RationalTaylor.nat_bits_le_self (2*n+1)).trans (by omega : 2*n+1≤2*N+1)
  have hp := (RationalAccumulator.bits_mul_le (b^(2*n+1)) (2*n+1)).trans (Nat.add_le_add hpow hn')
  unfold termDenominator termWidth
  nlinarith only [hp]

theorem denominator_bits (b n N W : ℕ) (hn : n≤N) (hb : b.bits.length≤W) :
    (denominator b n).bits.length≤n*termWidth N W+1 := by
  induction n with
  | zero => simp [denominator]
  | succ n ih =>
    have hp := (RationalAccumulator.bits_mul_le (termDenominator b n) (denominator b n)).trans
      (Nat.add_le_add (termDenominator_bits b n N W (by omega) hb) (ih (by omega)))
    change (termDenominator b n*denominator b n).bits.length≤_
    nlinarith only [hp]

theorem numerator_bits (a b : ℕ) (keep : ℕ→Bool) (n N W : ℕ) (hn : n≤N)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W) :
    (numerator a b keep n).bits.length≤n*(termWidth N W+1)+1 := by
  induction n with
  | zero => simp [numerator]
  | succ n ih =>
    have hnN : n≤N := by omega
    have hl := (RationalAccumulator.bits_mul_le (termDenominator b n) (numerator a b keep n)).trans
      (Nat.add_le_add (termDenominator_bits b n N W hnN hb) (ih hnN))
    have hr := (RationalAccumulator.bits_mul_le (a^(2*n+1)) (denominator b n)).trans
      (Nat.add_le_add (power_bits a n N W hnN ha) (denominator_bits b n N W hnN hb))
    change (termDenominator b n*numerator a b keep n+
      if keep n then a^(2*n+1)*denominator b n else 0).bits.length≤_
    cases keep n <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero]
    · nlinarith only [hl]
    · have hs := RationalAccumulator.bits_add_le
        (termDenominator b n*numerator a b keep n) (a^(2*n+1)*denominator b n)
      have hmax : max (termDenominator b n*numerator a b keep n).bits.length
          (a^(2*n+1)*denominator b n).bits.length≤(n+1)*(termWidth N W+1) :=
        max_le (by nlinarith only [hl]) (by nlinarith only [hr])
      nlinarith only [hs,hmax]

#print axioms arctanTaylor_eq
#print axioms numerator_bits

end Maxwell.Continuum.RationalArctan
