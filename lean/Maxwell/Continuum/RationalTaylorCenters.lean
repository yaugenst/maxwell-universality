import Maxwell.Continuum.RationalTaylorData

/-! The integer Taylor evaluator computes the centers of the literal
exponential, sine and cosine enclosures used by calibration. -/

namespace Maxwell.Continuum.RationalTaylor
open Maxwell.Certificate
set_option maxHeartbeats 1000000

def positiveSigns (_ : ℕ) : Sign := .plus
def negativeSigns (n : ℕ) : Sign := if n%2=0 then .plus else .minus
def cosineSigns (n : ℕ) : Sign := if n%4=0 then .plus else if n%4=2 then .minus else .zero
def sineSigns (n : ℕ) : Sign := if n%4=1 then .plus else if n%4=3 then .minus else .zero

theorem imaginarySigns_succ (n : ℕ) :
    (cosineSigns (n+1)).value = -(sineSigns n).value ∧
    (sineSigns (n+1)).value = (cosineSigns n).value := by
  have h : n%4<4 := Nat.mod_lt _ (by decide)
  interval_cases he : n%4 <;>
    have hn : (n+1)%4=(n%4+1)%4 := by omega
  all_goals simp [cosineSigns,sineSigns,Sign.value,hn,he]

theorem negativeSigns_succ (n : ℕ) :
    (negativeSigns (n+1)).value = -(negativeSigns n).value := by
  have h : n%2<2 := Nat.mod_lt _ (by decide)
  interval_cases he : n%2 <;>
    have hn : (n+1)%2=(n%2+1)%2 := by omega
  all_goals simp [negativeSigns,Sign.value,hn,he]

theorem negativeSigns_value (n : ℕ) : (negativeSigns n).value=(-1:ℚ)^n := by
  induction n with
  | zero => simp [negativeSigns,Sign.value]
  | succ n ih => rw [negativeSigns_succ,ih,pow_succ]; ring

theorem power_real_centers (q : ℚ) (n : ℕ) :
    (ComplexRectangle.power (ComplexRectangle.point q 0) n).re.center=q^n ∧
    (ComplexRectangle.power (ComplexRectangle.point q 0) n).im.center=0 := by
  induction n with
  | zero => simp [ComplexRectangle.power,ComplexRectangle.point]
  | succ n ih =>
    change ((ComplexRectangle.power (ComplexRectangle.point q 0) n).re.center*q+
      -((ComplexRectangle.power (ComplexRectangle.point q 0) n).im.center*0)=q^(n+1)) ∧
      (ComplexRectangle.power (ComplexRectangle.point q 0) n).re.center*0+
      (ComplexRectangle.power (ComplexRectangle.point q 0) n).im.center*q=0
    rw [ih.1,ih.2]
    simp [pow_succ]

theorem power_imaginary_centers (q : ℚ) (n : ℕ) :
    (ComplexRectangle.power (ComplexRectangle.point 0 q) n).re.center=(cosineSigns n).value*q^n ∧
    (ComplexRectangle.power (ComplexRectangle.point 0 q) n).im.center=(sineSigns n).value*q^n := by
  induction n with
  | zero => simp [ComplexRectangle.power,ComplexRectangle.point,cosineSigns,sineSigns,Sign.value]
  | succ n ih =>
    change ((ComplexRectangle.power (ComplexRectangle.point 0 q) n).re.center*0+
      -((ComplexRectangle.power (ComplexRectangle.point 0 q) n).im.center*q)=_) ∧
      (ComplexRectangle.power (ComplexRectangle.point 0 q) n).re.center*q+
      (ComplexRectangle.power (ComplexRectangle.point 0 q) n).im.center*0=_
    rw [ih.1,ih.2,(imaginarySigns_succ n).1,(imaginarySigns_succ n).2,pow_succ]
    constructor <;> ring

theorem expTaylor_real_center (q : ℚ) (n : ℕ) :
    (ComplexRectangle.expTaylor (ComplexRectangle.point q 0) n).re.center=
      ∑ k ∈ Finset.range n, q^k/(k.factorial:ℚ) := by
  induction n with
  | zero => simp [ComplexRectangle.expTaylor,ComplexRectangle.point]
  | succ n ih =>
    change (ComplexRectangle.expTaylor (ComplexRectangle.point q 0) n).re.center+
      ((ComplexRectangle.power (ComplexRectangle.point q 0) n).re.center*(1/(n.factorial:ℚ))+
      -((ComplexRectangle.power (ComplexRectangle.point q 0) n).im.center*0))=_
    rw [ih,(power_real_centers q n).1]
    simp [Finset.sum_range_succ,div_eq_mul_inv]

theorem expTaylor_imaginary_centers (q : ℚ) (n : ℕ) :
    (ComplexRectangle.expTaylor (ComplexRectangle.point 0 q) n).re.center=
      (∑ k ∈ Finset.range n, (cosineSigns k).value*q^k/(k.factorial:ℚ)) ∧
    (ComplexRectangle.expTaylor (ComplexRectangle.point 0 q) n).im.center=
      ∑ k ∈ Finset.range n, (sineSigns k).value*q^k/(k.factorial:ℚ) := by
  induction n with
  | zero => simp [ComplexRectangle.expTaylor,ComplexRectangle.point]
  | succ n ih =>
    change ((ComplexRectangle.expTaylor (ComplexRectangle.point 0 q) n).re.center+
      ((ComplexRectangle.power (ComplexRectangle.point 0 q) n).re.center*(1/(n.factorial:ℚ))+
      -((ComplexRectangle.power (ComplexRectangle.point 0 q) n).im.center*0))=_) ∧
      (ComplexRectangle.expTaylor (ComplexRectangle.point 0 q) n).im.center+
      ((ComplexRectangle.power (ComplexRectangle.point 0 q) n).re.center*0+
      (ComplexRectangle.power (ComplexRectangle.point 0 q) n).im.center*(1/(n.factorial:ℚ)))=_
    rw [ih.1,ih.2,(power_imaginary_centers q n).1,(power_imaginary_centers q n).2]
    simp [Finset.sum_range_succ,div_eq_mul_inv]

private theorem order_sub_add (B P : ℕ) : Calibration.taylorOrder B P-1+1=Calibration.taylorOrder B P := by
  unfold Calibration.taylorOrder Calibration.taylorHalfOrder
  omega

theorem positive_expApprox_center (a b : ℕ) (hb : 0<b) (B P : ℕ) :
    (Elementary.expApprox ((a:ℚ)/b) B P).center=
      value a b positiveSigns (Calibration.taylorOrder B P-1) := by
  rw [value_sum a b hb,order_sub_add]
  change (ComplexRectangle.expTaylor (ComplexRectangle.point ((a:ℚ)/b) 0) _).re.center=_
  rw [expTaylor_real_center]
  simp only [positiveSigns,Sign.value,one_mul]

theorem negative_expApprox_center (a b : ℕ) (hb : 0<b) (B P : ℕ) :
    (Elementary.expApprox (-((a:ℚ)/b)) B P).center=
      value a b negativeSigns (Calibration.taylorOrder B P-1) := by
  rw [value_sum a b hb,order_sub_add]
  change (ComplexRectangle.expTaylor (ComplexRectangle.point (-((a:ℚ)/b)) 0) _).re.center=_
  rw [expTaylor_real_center]
  apply Finset.sum_congr rfl
  intro k _
  rw [negativeSigns_value,neg_pow]

theorem cosApprox_center (a b : ℕ) (hb : 0<b) (B P : ℕ) :
    (Elementary.cosApprox ((a:ℚ)/b) B P).center=
      value a b cosineSigns (Calibration.taylorOrder B P-1) := by
  rw [value_sum a b hb,order_sub_add]
  exact (expTaylor_imaginary_centers ((a:ℚ)/b) (Calibration.taylorOrder B P)).1

theorem sinApprox_center (a b : ℕ) (hb : 0<b) (B P : ℕ) :
    (Elementary.sinApprox ((a:ℚ)/b) B P).center=
      value a b sineSigns (Calibration.taylorOrder B P-1) := by
  rw [value_sum a b hb,order_sub_add]
  exact (expTaylor_imaginary_centers ((a:ℚ)/b) (Calibration.taylorOrder B P)).2

#print axioms negative_expApprox_center
#print axioms cosApprox_center
#print axioms sinApprox_center

end Maxwell.Continuum.RationalTaylor
