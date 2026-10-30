import Maxwell.Continuum.RationalArctanProgram
import Maxwell.Continuum.RationalWordBounds

/-! The literal Machin center represented by three bounded integer words. -/

namespace Maxwell.Continuum.Machin
open RationalTaylor Maxwell.Certificate
set_option maxHeartbeats 1000000

def positive (b N : ℕ) : ℕ :=
  RationalArctan.numerator 1 b (fun k => (negativeSigns k).positive) (N+6)
def negative (b N : ℕ) : ℕ :=
  RationalArctan.numerator 1 b (fun k => (negativeSigns k).negative) (N+6)
def denominator (b N : ℕ) : ℕ := RationalArctan.denominator b (N+6)

def numeratorPositive (N : ℕ) : ℕ :=
  16*positive 5 N*denominator 239 N+4*negative 239 N*denominator 5 N
def numeratorNegative (N : ℕ) : ℕ :=
  16*negative 5 N*denominator 239 N+4*positive 239 N*denominator 5 N
def commonDenominator (N : ℕ) : ℕ := denominator 5 N*denominator 239 N
def wordWidth (N : ℕ) : ℕ := 2*RationalArctan.width (N+6) 8+6

theorem commonDenominator_pos (N : ℕ) : 0<commonDenominator N :=
  Nat.mul_pos (RationalArctan.denominator_pos (by decide : 0<5) _)
    (RationalArctan.denominator_pos (by decide : 0<239) _)

theorem piApprox_center (N : ℕ) :
    (Elementary.piApprox N).center=
      ((numeratorPositive N:ℚ)-numeratorNegative N)/commonDenominator N := by
  have h5 : (denominator 5 N:ℚ)≠0 := by
    exact_mod_cast (RationalArctan.denominator_pos (by decide : 0<5) (N+6)).ne'
  have h239 : (denominator 239 N:ℚ)≠0 := by
    exact_mod_cast (RationalArctan.denominator_pos (by decide : 0<239) (N+6)).ne'
  change 16*Elementary.arctanTaylor ((1:ℚ)/5) (N+6)-
    4*Elementary.arctanTaylor ((1:ℚ)/239) (N+6)=_
  have e5 := RationalArctan.arctanTaylor_eq 1 5 (by decide) (N+6)
  have e239 := RationalArctan.arctanTaylor_eq 1 239 (by decide) (N+6)
  norm_num only [Nat.cast_one,Nat.cast_ofNat] at e5 e239
  rw [e5,e239]
  change 16*(((positive 5 N:ℚ)-negative 5 N)/denominator 5 N)-
    4*(((positive 239 N:ℚ)-negative 239 N)/denominator 239 N)=_
  simp only [numeratorPositive,numeratorNegative,commonDenominator,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  field_simp
  ring

theorem prefix_width (b N : ℕ) (hb : b.bits.length≤8) :
    (positive b N).bits.length≤RationalArctan.width (N+6) 8 ∧
    (negative b N).bits.length≤RationalArctan.width (N+6) 8 ∧
    (denominator b N).bits.length≤RationalArctan.width (N+6) 8 := by
  have hw := RationalArctan.values_width 1 b negativeSigns (N+6) (N+6) 8 le_rfl (by decide) hb
  constructor
  · simpa [RationalArctan.values,positive] using hw 612
  constructor
  · simpa [RationalArctan.values,negative] using hw 613
  · simpa [RationalArctan.values,denominator] using hw 614

theorem parts_width (N : ℕ) :
    (numeratorPositive N).bits.length≤wordWidth N ∧
    (numeratorNegative N).bits.length≤wordWidth N ∧
    (commonDenominator N).bits.length≤wordWidth N := by
  have h5 := prefix_width 5 N (by decide)
  have h239 := prefix_width 239 N (by decide)
  have product (c x y : ℕ) (hc : c.bits.length≤5)
      (hx : x.bits.length≤RationalArctan.width (N+6) 8)
      (hy : y.bits.length≤RationalArctan.width (N+6) 8) :
      (c*x*y).bits.length≤2*RationalArctan.width (N+6) 8+5 := by
    have h := (Maxwell.Cost.RationalAccumulator.bits_mul_le (c*x) y).trans
      (Nat.add_le_add ((Maxwell.Cost.RationalAccumulator.bits_mul_le c x).trans
        (Nat.add_le_add hc hx)) hy)
    omega
  have sum_bound (a b : ℕ)
      (ha : a.bits.length≤2*RationalArctan.width (N+6) 8+5)
      (hb : b.bits.length≤2*RationalArctan.width (N+6) 8+5) :
      (a+b).bits.length≤wordWidth N := by
    have h := Maxwell.Cost.RationalAccumulator.bits_add_le a b
    unfold wordWidth
    omega
  refine ⟨sum_bound _ _ (product 16 _ _ (by decide) h5.1 h239.2.2)
      (product 4 _ _ (by decide) h239.2.1 h5.2.2),
    sum_bound _ _ (product 16 _ _ (by decide) h5.2.1 h239.2.2)
      (product 4 _ _ (by decide) h239.1 h5.2.2),?_⟩
  have h := (Maxwell.Cost.RationalAccumulator.bits_mul_le (denominator 5 N) (denominator 239 N)).trans
    (Nat.add_le_add h5.2.2 h239.2.2)
  unfold commonDenominator wordWidth
  omega

theorem wordWidth_bound (N : ℕ) : wordWidth N≤2^12*(N+1)^2 := by
  unfold wordWidth RationalArctan.width RationalArctan.termWidth
  nlinarith

theorem piApprox_word_bits (N : ℕ) :
    (Elementary.piApprox N).center.num.natAbs.bits.length≤2^13*(N+1)^2 ∧
    (Elementary.piApprox N).center.den.bits.length≤2^13*(N+1)^2 := by
  rw [piApprox_center]
  have hp := parts_width N
  have h := RationalWords.parts_width _ _ _ (wordWidth N) (commonDenominator_pos N) hp.1 hp.2.1 hp.2.2
  have hb := wordWidth_bound N
  have h1 : 1≤(N+1)^2 := one_le_pow₀ (by omega)
  constructor <;> nlinarith only [h.1,h.2,hb,h1]

#print axioms piApprox_center
#print axioms piApprox_word_bits

end Maxwell.Continuum.Machin
