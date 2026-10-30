import Maxwell.Continuum.RationalTaylorCenters
import Maxwell.Continuum.RationalArithmeticWidths

/-! Signed rational inputs for the executable common-denominator Taylor evaluator. -/

namespace Maxwell.Continuum.RationalTaylor
open Maxwell.Certificate
set_option maxHeartbeats 1000000

def Sign.product : Sign → Sign → Sign
  | .zero, _ => .zero
  | _, .zero => .zero
  | .plus, s => s
  | .minus, .plus => .minus
  | .minus, .minus => .plus

theorem Sign.product_value (a b : Sign) : (a.product b).value=a.value*b.value := by
  cases a <;> cases b <;> norm_num [Sign.product,Sign.value]

def argumentSigns (q : ℚ) (base : ℕ → Sign) (n : ℕ) : Sign :=
  (base n).product (if q.num<0 then negativeSigns n else positiveSigns n)

theorem argumentSigns_power (q : ℚ) (base : ℕ → Sign) (n : ℕ) :
    (argumentSigns q base n).value*((q.num.natAbs:ℚ)/q.den)^n=(base n).value*q^n := by
  unfold argumentSigns
  rw [Sign.product_value]
  by_cases h : q.num<0
  · rw [ite_eq_left h,negativeSigns_value]
    have he : q=-((q.num.natAbs:ℚ)/q.den) := by
      have hn : (q.num:ℚ)=-(q.num.natAbs:ℚ) := by
        exact_mod_cast Int.eq_neg_natAbs_of_nonpos h.le
      calc
        q = (q.num:ℚ)/q.den := q.num_div_den.symm
        _ = _ := by rw [hn]; ring
    calc
      _ = (base n).value*(-((q.num.natAbs:ℚ)/q.den))^n := by rw [neg_pow]; ring
      _ = _ := congrArg (fun x : ℚ => (base n).value*x^n) he.symm
  · rw [ite_eq_right h]
    have he : q=(q.num.natAbs:ℚ)/q.den := by
      have hn : (q.num:ℚ)=(q.num.natAbs:ℚ) := by
        simpa only [Int.cast_natCast] using
          congrArg (fun z : ℤ => (z:ℚ)) (Int.eq_natAbs_of_nonneg (le_of_not_gt h))
      calc
        q = (q.num:ℚ)/q.den := q.num_div_den.symm
        _ = _ := by rw [hn]
    simp only [positiveSigns,Sign.value,mul_one]
    exact congrArg (fun x : ℚ => (base n).value*x^n) he.symm

theorem signed_value_sum (q : ℚ) (base : ℕ → Sign) (n : ℕ) :
    value q.num.natAbs q.den (argumentSigns q base) n=
      ∑ k ∈ Finset.range (n+1), (base k).value*q^k/(k.factorial:ℚ) := by
  rw [value_sum _ _ q.den_pos]
  apply Finset.sum_congr rfl
  intro k _
  rw [argumentSigns_power]

private theorem order_sub_add (B P : ℕ) :
    Calibration.taylorOrder B P-1+1=Calibration.taylorOrder B P := by
  unfold Calibration.taylorOrder Calibration.taylorHalfOrder
  omega

theorem signed_expApprox_center (q : ℚ) (B P : ℕ) :
    (Elementary.expApprox q B P).center=
      value q.num.natAbs q.den (argumentSigns q positiveSigns) (Calibration.taylorOrder B P-1) := by
  rw [signed_value_sum,order_sub_add]
  change (ComplexRectangle.expTaylor (ComplexRectangle.point q 0) _).re.center=_
  rw [expTaylor_real_center]
  simp only [positiveSigns,Sign.value,one_mul]

theorem signed_cosApprox_center (q : ℚ) (B P : ℕ) :
    (Elementary.cosApprox q B P).center=
      value q.num.natAbs q.den (argumentSigns q cosineSigns) (Calibration.taylorOrder B P-1) := by
  rw [signed_value_sum,order_sub_add]
  exact (expTaylor_imaginary_centers q (Calibration.taylorOrder B P)).1

theorem signed_sinApprox_center (q : ℚ) (B P : ℕ) :
    (Elementary.sinApprox q B P).center=
      value q.num.natAbs q.den (argumentSigns q sineSigns) (Calibration.taylorOrder B P-1) := by
  rw [signed_value_sum,order_sub_add]
  exact (expTaylor_imaginary_centers q (Calibration.taylorOrder B P)).2

theorem signed_value_width {q : ℚ} {W : ℕ} (hq : RationalWords.Width q W)
    (base : ℕ → Sign) (N : ℕ) :
    RationalWords.Width (value q.num.natAbs q.den (argumentSigns q base) N) (width N W+1) := by
  have hp := numerator_bits q.num.natAbs q.den
    (fun k => (argumentSigns q base k).positive) N W hq.num hq.den N le_rfl
  have hn := numerator_bits q.num.natAbs q.den
    (fun k => (argumentSigns q base k).negative) N W hq.num hq.den N le_rfl
  have hd := denominator_bits q.den N N W le_rfl hq.den
  have hh := RationalWords.parts_width _ _ _ (width N W)
    (denominator_pos q.den_pos N) hp hn hd
  exact ⟨hh.1,hh.2.trans (Nat.le_succ _)⟩

#print axioms signed_expApprox_center
#print axioms signed_cosApprox_center
#print axioms signed_value_width

end Maxwell.Continuum.RationalTaylor
