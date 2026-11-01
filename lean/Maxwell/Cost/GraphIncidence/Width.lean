import Maxwell.Cost.GraphIncidence.Complexity
import Maxwell.Cost.RationalAccumulator.Move

/-! The incidence traversal's descriptor widths are logarithmic in its
array dimensions and linear in the endpoint word width. -/
namespace Maxwell.Cost.GraphIncidence
open RationalAccumulator

theorem descriptor_width (w d e : ℕ) :
    IncidencePass.budget (layout w d e) (4*e).bits+(w+3)+6≤
      20*(w+d.bits.length+e.bits.length+10) := by
  have word : w.bits.length≤w:=by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact Nat.lt_two_pow_self
  have endpoint:=bits_add_le w 3
  have count:=bits_mul_le 4 e
  have array:=bits_mul_le (4*e) (w+3)
  have twice:=bits_mul_le 2 d
  have vertices:=bits_add_le (2*d) e
  have counter:=bits_mul_le 2 (2*d+e)
  have rank:=bits_add_le (4*e*(w+3)) (2*(2*d+e))
  simp only [show (3:ℕ).bits.length=2 by decide] at endpoint
  simp only [show (4:ℕ).bits.length=3 by decide] at count
  simp only [show (2:ℕ).bits.length=2 by decide] at twice counter
  change (w+3)+(w+3).bits.length+(4*e).bits.length+0+
    (4*e*(w+3)).bits.length+(4*e*(w+3)+2*(2*d+e)).bits.length+10+(w+3)+6≤_
  omega

#print axioms descriptor_width
end Maxwell.Cost.GraphIncidence
