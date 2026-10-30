import Maxwell.Continuum.RationalArithmeticWidths
import Maxwell.Continuum.RationalMagnitudeMachine

/-! Unreduced runtime rational values for a shared-register dataflow evaluator. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost
set_option maxHeartbeats 1500000

structure Parts where
  positive : ℕ
  negative : ℕ
  denominator : ℕ
  deriving DecidableEq, Repr

namespace Parts

def value (x : Parts) : ℚ := ((x.positive:ℚ)-x.negative)/x.denominator
def Valid (x : Parts) : Prop := 0<x.denominator
def Width (x : Parts) (B : ℕ) : Prop :=
  x.positive.bits.length≤B ∧ x.negative.bits.length≤B ∧ x.denominator.bits.length≤B

def literal (q : ℚ) : Parts := ⟨q.num.toNat,(-q.num).toNat,q.den⟩
def add (x y : Parts) : Parts :=
  ⟨x.positive*y.denominator+y.positive*x.denominator,
   x.negative*y.denominator+y.negative*x.denominator,x.denominator*y.denominator⟩
def sub (x y : Parts) : Parts :=
  ⟨x.positive*y.denominator+y.negative*x.denominator,
   x.negative*y.denominator+y.positive*x.denominator,x.denominator*y.denominator⟩
def mul (x y : Parts) : Parts :=
  ⟨x.positive*y.positive+x.negative*y.negative,
   x.positive*y.negative+x.negative*y.positive,x.denominator*y.denominator⟩
def inverse (x : Parts) : Parts :=
  if x.positive<x.negative then
    ⟨0,x.denominator,IntegerNormSquare.magnitude x.positive x.negative⟩
  else ⟨x.denominator,0,IntegerNormSquare.magnitude x.positive x.negative⟩

theorem literal_value (q : ℚ) : (literal q).value=q := by
  have h : (q.num.toNat:ℚ)-((-q.num).toNat:ℚ)=(q.num:ℚ) := by
    exact_mod_cast Int.toNat_sub_toNat_neg q.num
  unfold literal value
  rw [h,q.num_div_den]

theorem literal_valid (q : ℚ) : (literal q).Valid := q.den_pos

theorem add_value (x y : Parts) (hx : x.Valid) (hy : y.Valid) : (x.add y).value=x.value+y.value := by
  have hx0 : (x.denominator:ℚ)≠0 := by exact_mod_cast hx.ne'
  have hy0 : (y.denominator:ℚ)≠0 := by exact_mod_cast hy.ne'
  unfold add value
  push_cast
  field_simp
  ring

theorem sub_value (x y : Parts) (hx : x.Valid) (hy : y.Valid) : (x.sub y).value=x.value-y.value := by
  have hx0 : (x.denominator:ℚ)≠0 := by exact_mod_cast hx.ne'
  have hy0 : (y.denominator:ℚ)≠0 := by exact_mod_cast hy.ne'
  unfold sub value
  push_cast
  field_simp
  ring

theorem mul_value (x y : Parts) : (x.mul y).value=x.value*y.value := by
  unfold mul value
  push_cast
  rw [div_mul_div_comm]
  congr 1
  ring

theorem add_valid {x y : Parts} (hx : x.Valid) (hy : y.Valid) : (x.add y).Valid := Nat.mul_pos hx hy
theorem sub_valid {x y : Parts} (hx : x.Valid) (hy : y.Valid) : (x.sub y).Valid := Nat.mul_pos hx hy
theorem mul_valid {x y : Parts} (hx : x.Valid) (hy : y.Valid) : (x.mul y).Valid := Nat.mul_pos hx hy

theorem magnitude_eq_of_lt (x : Parts) (h : x.positive<x.negative) :
    IntegerNormSquare.magnitude x.positive x.negative=x.negative-x.positive := by
  have he : (x.positive:ℤ)-x.negative=-((x.negative-x.positive:ℕ):ℤ) := by omega
  unfold IntegerNormSquare.magnitude
  rw [he,Int.natAbs_neg,Int.natAbs_natCast]

theorem magnitude_eq_of_le (x : Parts) (h : x.negative≤x.positive) :
    IntegerNormSquare.magnitude x.positive x.negative=x.positive-x.negative := by
  have he : (x.positive:ℤ)-x.negative=((x.positive-x.negative:ℕ):ℤ) := by omega
  unfold IntegerNormSquare.magnitude
  rw [he,Int.natAbs_natCast]

theorem channels_ne_of_value_ne {x : Parts} (h : x.value≠0) : x.positive≠x.negative := by
  intro he
  apply h
  simp only [value,he,sub_self,zero_div]

theorem inverse_valid {x : Parts} (h : x.value≠0) : x.inverse.Valid := by
  have hn := channels_ne_of_value_ne h
  unfold inverse Valid
  split_ifs with hp
  · change 0<IntegerNormSquare.magnitude _ _
    rw [magnitude_eq_of_lt x hp]
    omega
  · change 0<IntegerNormSquare.magnitude _ _
    rw [magnitude_eq_of_le x (by omega)]
    omega

theorem inverse_value (x : Parts) (hx : x.Valid) (hn : x.value≠0) : x.inverse.value=x.value⁻¹ := by
  have hne := channels_ne_of_value_ne hn
  have hd : (x.denominator:ℚ)≠0 := by exact_mod_cast hx.ne'
  unfold inverse
  split_ifs with hp
  · rw [show (⟨0,x.denominator,IntegerNormSquare.magnitude x.positive x.negative⟩:Parts).value=
        -(x.denominator:ℚ)/(IntegerNormSquare.magnitude x.positive x.negative) by simp [value]]
    rw [magnitude_eq_of_lt x hp,Nat.cast_sub hp.le]
    unfold value
    rw [inv_div]
    have he : (x.positive:ℚ)≠(x.negative:ℚ) := by exact_mod_cast hne
    have hc : (x.positive:ℚ)-(x.negative:ℚ)≠0 := sub_ne_zero.mpr he
    have hc' : (x.negative:ℚ)-(x.positive:ℚ)≠0 := sub_ne_zero.mpr he.symm
    field_simp
    ring
  · rw [show (⟨x.denominator,0,IntegerNormSquare.magnitude x.positive x.negative⟩:Parts).value=
        (x.denominator:ℚ)/(IntegerNormSquare.magnitude x.positive x.negative) by simp [value]]
    rw [magnitude_eq_of_le x (by omega),Nat.cast_sub (by omega : x.negative≤x.positive)]
    unfold value
    rw [inv_div]

theorem Width.mono {x : Parts} {B C : ℕ} (h : x.Width B) (hBC : B≤C) : x.Width C :=
  ⟨h.1.trans hBC,h.2.1.trans hBC,h.2.2.trans hBC⟩

private theorem productSum_bits {a b c d B C : ℕ}
    (ha : a.bits.length≤B) (hb : b.bits.length≤C) (hc : c.bits.length≤B) (hd : d.bits.length≤C) :
    (a*b+c*d).bits.length≤B+C+1 := by
  have h1 := (RationalAccumulator.bits_mul_le a b).trans (Nat.add_le_add ha hb)
  have h2 := (RationalAccumulator.bits_mul_le c d).trans (Nat.add_le_add hc hd)
  exact (RationalAccumulator.bits_add_le _ _).trans (Nat.add_le_add_right (max_le h1 h2) 1)

theorem Width.add {x y : Parts} {B C : ℕ} (hx : x.Width B) (hy : y.Width C) : (x.add y).Width (B+C+1) := by
  have hp : (x.positive*y.denominator+y.positive*x.denominator).bits.length≤B+C+1 := by
    rw [Nat.mul_comm y.positive x.denominator]
    exact productSum_bits hx.1 hy.2.2 hx.2.2 hy.1
  have hn : (x.negative*y.denominator+y.negative*x.denominator).bits.length≤B+C+1 := by
    rw [Nat.mul_comm y.negative x.denominator]
    exact productSum_bits hx.2.1 hy.2.2 hx.2.2 hy.2.1
  exact ⟨hp,hn,((RationalAccumulator.bits_mul_le _ _).trans (Nat.add_le_add hx.2.2 hy.2.2)).trans (Nat.le_succ _)⟩

theorem Width.sub {x y : Parts} {B C : ℕ} (hx : x.Width B) (hy : y.Width C) : (x.sub y).Width (B+C+1) := by
  have hp : (x.positive*y.denominator+y.negative*x.denominator).bits.length≤B+C+1 := by
    rw [Nat.mul_comm y.negative x.denominator]
    exact productSum_bits hx.1 hy.2.2 hx.2.2 hy.2.1
  have hn : (x.negative*y.denominator+y.positive*x.denominator).bits.length≤B+C+1 := by
    rw [Nat.mul_comm y.positive x.denominator]
    exact productSum_bits hx.2.1 hy.2.2 hx.2.2 hy.1
  exact ⟨hp,hn,((RationalAccumulator.bits_mul_le _ _).trans (Nat.add_le_add hx.2.2 hy.2.2)).trans (Nat.le_succ _)⟩

theorem Width.mul {x y : Parts} {B C : ℕ} (hx : x.Width B) (hy : y.Width C) : (x.mul y).Width (B+C+1) :=
  ⟨productSum_bits hx.1 hy.1 hx.2.1 hy.2.1,productSum_bits hx.1 hy.2.1 hx.2.1 hy.1,
    ((RationalAccumulator.bits_mul_le _ _).trans (Nat.add_le_add hx.2.2 hy.2.2)).trans (Nat.le_succ _)⟩

theorem Width.inverse {x : Parts} {B : ℕ} (hx : x.Width B) : x.inverse.Width (B+1) := by
  have hm := (IntegerNormSquare.magnitude_bits_length_le x.positive x.negative).trans
    (Nat.add_le_add_right (max_le hx.1 hx.2.1) 1)
  unfold Parts.inverse Width
  split_ifs <;> simp only
  · exact ⟨by simp,hx.2.2.trans (Nat.le_succ _),hm⟩
  · exact ⟨hx.2.2.trans (Nat.le_succ _),by simp,hm⟩

theorem literal_width {q : ℚ} {B : ℕ} (h : RationalWords.Width q B) : (literal q).Width B := by
  have he := Int.toNat_add_toNat_neg_eq_natAbs q.num
  have hp : q.num.toNat≤q.num.natAbs := by omega
  have hn : (-q.num).toNat≤q.num.natAbs := by omega
  exact ⟨(RationalWords.bits_mono hp).trans h.num,(RationalWords.bits_mono hn).trans h.num,h.den⟩

end Parts

#print axioms Parts.inverse_value
#print axioms Parts.Width.mul
#print axioms Parts.literal_width

end Maxwell.Continuum.RationalDataflow
