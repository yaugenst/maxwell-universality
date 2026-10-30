import Maxwell.Continuum.RationalTaylorSignedInputs

/-! Exact Taylor centers on signed, not necessarily reduced, rational input words. -/

namespace Maxwell.Continuum.RationalTaylor
open Maxwell.Certificate
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
attribute [local irreducible] Elementary.expApprox Elementary.cosApprox Elementary.sinApprox

def signedFraction (negative : Bool) (a b : ℕ) : ℚ := if negative then -((a:ℚ)/b) else (a:ℚ)/b
def fractionSigns (negative : Bool) (base : ℕ→Sign) (n : ℕ) : Sign :=
  (base n).product (if negative then negativeSigns n else positiveSigns n)

theorem fractionSigns_power (negative : Bool) (a b : ℕ) (base : ℕ→Sign) (n : ℕ) :
    (fractionSigns negative base n).value*((a:ℚ)/b)^n=(base n).value*(signedFraction negative a b)^n := by
  cases negative with
  | false =>
    change ((base n).product .plus).value*((a:ℚ)/b)^n=(base n).value*((a:ℚ)/b)^n
    rw [Sign.product_value]
    simp only [Sign.value,mul_one]
  | true =>
    change ((base n).product (negativeSigns n)).value*((a:ℚ)/b)^n=(base n).value*(-((a:ℚ)/b))^n
    rw [Sign.product_value,negativeSigns_value,neg_pow]
    ring

theorem fraction_value_sum (negative : Bool) (a b : ℕ) (hb : 0<b) (base : ℕ→Sign) (N : ℕ) :
    value a b (fractionSigns negative base) N=
      ∑ k∈Finset.range (N+1), (base k).value*(signedFraction negative a b)^k/(k.factorial:ℚ) := by
  rw [value_sum _ _ hb]
  apply Finset.sum_congr rfl
  intro k _
  rw [fractionSigns_power]

private theorem order_sub_add (B P : ℕ) :
    Calibration.taylorOrder B P-1+1=Calibration.taylorOrder B P := by
  unfold Calibration.taylorOrder Calibration.taylorHalfOrder
  omega

theorem fraction_expApprox_center (negative : Bool) (a b : ℕ) (hb : 0<b) (B P : ℕ) :
    (Elementary.expApprox (signedFraction negative a b) B P).center=
      value a b (fractionSigns negative positiveSigns) (Calibration.taylorOrder B P-1) := by
  rw [fraction_value_sum _ _ _ hb,order_sub_add]
  unfold Elementary.expApprox
  change (ComplexRectangle.expTaylor (ComplexRectangle.point (signedFraction negative a b) 0) _).re.center=_
  rw [expTaylor_real_center]
  simp only [positiveSigns,Sign.value,one_mul]

theorem fraction_cosApprox_center (negative : Bool) (a b : ℕ) (hb : 0<b) (B P : ℕ) :
    (Elementary.cosApprox (signedFraction negative a b) B P).center=
      value a b (fractionSigns negative cosineSigns) (Calibration.taylorOrder B P-1) := by
  rw [fraction_value_sum _ _ _ hb,order_sub_add]
  unfold Elementary.cosApprox
  exact (expTaylor_imaginary_centers (signedFraction negative a b) (Calibration.taylorOrder B P)).1

theorem fraction_sinApprox_center (negative : Bool) (a b : ℕ) (hb : 0<b) (B P : ℕ) :
    (Elementary.sinApprox (signedFraction negative a b) B P).center=
      value a b (fractionSigns negative sineSigns) (Calibration.taylorOrder B P-1) := by
  rw [fraction_value_sum _ _ _ hb,order_sub_add]
  unfold Elementary.sinApprox
  exact (expTaylor_imaginary_centers (signedFraction negative a b) (Calibration.taylorOrder B P)).2

#print axioms fraction_cosApprox_center
#print axioms fraction_sinApprox_center

end Maxwell.Continuum.RationalTaylor
