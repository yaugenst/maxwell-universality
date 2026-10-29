import Maxwell.Cost.Structured.NatAssign
import Maxwell.Cost.RationalAccumulator.Move

namespace Maxwell.Cost.Structured.NatAssign

def Instruction.literalWidth : Instruction → ℕ
  | .literal _ n => n.bits.length
  | _ => 0

theorem instruction_width (ids : Finset ℕ) (a : Instruction) (hv : a.Valid ids)
    (v : ℕ → ℕ) (B : ℕ) (hb : ∀ i ∈ ids, (v i).bits.length ≤ B)
    (hc : a.literalWidth ≤ B) :
    ∀ i ∈ ids, (a.update v i).bits.length ≤ 2*B+1 := by
  intro i hi
  by_cases he : i=a.target
  · subst i
    simp only [Instruction.update,Function.update_self]
    cases a with
    | literal target n => simpa only [Instruction.literalWidth,Instruction.value] using hc.trans (by omega)
    | copy source target => exact (hb source hv.1).trans (by omega)
    | add source target =>
      have hx := hb source hv.1
      have hy := hb target hv.2.1
      have hh := RationalAccumulator.bits_add_le (v source) (v target)
      change (v source+v target).bits.length ≤ _
      omega
    | multiply source target =>
      have hx := hb source hv.1
      have hy := hb target hv.2.1
      have hh := RationalAccumulator.bits_mul_le (v source) (v target)
      change (v source*v target).bits.length ≤ _
      omega
  · simp only [Instruction.update,Function.update_of_ne he]
    exact (hb i hi).trans (by omega)

theorem instruction_price_bound (ids : Finset ℕ) (a : Instruction) (hv : a.Valid ids)
    (v : ℕ → ℕ) (B : ℕ) (hb : ∀ i ∈ ids, (v i).bits.length ≤ B)
    (hc : a.literalWidth ≤ B) : a.price v ≤ 2400*(B+2)^2 := by
  cases a with
  | literal target n =>
    have hx := hb target hv
    change n.bits.length ≤ B at hc
    dsimp [Instruction.price]
    nlinarith
  | copy source target =>
    have hx := hb source hv.1
    have hy := hb target hv.2.1
    dsimp [Instruction.price]
    nlinarith
  | add source target =>
    have hx := hb source hv.1
    have hy := hb target hv.2.1
    dsimp [Instruction.price]
    nlinarith
  | multiply source target =>
    have hx := hb source hv.1
    have hy := hb target hv.2.1
    have h := Nat.pow_le_pow_left (show (v source).bits.length+(v target).bits.length+3 ≤ 2*(B+2) by omega) 2
    dsimp [Instruction.price]
    nlinarith only [h]

/-- A fixed arithmetic descriptor program has quadratic cost in the
input word width. The constant depends only on its finite instruction list. -/
theorem price_bound (ids : Finset ℕ) (instructions : List Instruction)
    (hv : ∀ a ∈ instructions, a.Valid ids) (v : ℕ → ℕ) (B : ℕ)
    (hb : ∀ i ∈ ids, (v i).bits.length ≤ B)
    (hc : ∀ a ∈ instructions, a.literalWidth ≤ B) :
    price instructions v ≤ 3000*8^instructions.length*(B+2)^2 := by
  induction instructions generalizing v B with
  | nil =>
    have h : 1 ≤ (B+2)^2 := Nat.one_le_pow _ _ (by omega)
    simp only [price,List.length_nil,pow_zero,mul_one]
    omega
  | cons a rest ih =>
    have ha := instruction_price_bound ids a (hv a (by simp)) v B hb (hc a (by simp))
    have hh := ih (fun a h => hv a (by simp [h])) (a.update v) (2*B+1)
      (instruction_width ids a (hv a (by simp)) v B hb (hc a (by simp)))
      (fun a h => (hc a (by simp [h])).trans (by omega))
    have hm : 1 ≤ 8^rest.length := Nat.one_le_pow _ _ (by decide)
    have hq : (2*B+1+2)^2 ≤ 4*(B+2)^2 := by
      calc
        (2*B+1+2)^2 ≤ (2*(B+2))^2 := Nat.pow_le_pow_left (by omega) 2
        _ = 4*(B+2)^2 := by ring
    have htail := Nat.mul_le_mul_left (3000*8^rest.length) hq
    have hbase := Nat.mul_le_mul_right ((B+2)^2) hm
    simp only [price,List.length_cons,pow_succ]
    nlinarith only [ha,hh,htail,hbase]

end Maxwell.Cost.Structured.NatAssign
