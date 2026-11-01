import Maxwell.Continuum.ParameterBufferMachineData
import Maxwell.Codec.NaturalLength

namespace Maxwell.Continuum.Parameters.BufferMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

structure Data.Width (D : Data) (B : ℕ) : Prop where
  constant : D.constant.bits.length ≤ B
  length : D.length.bits.length ≤ B
  wells : D.wells.bits.length ≤ B
  sourceSize : D.sourceSize.bits.length ≤ B
  conditionNum : D.conditionNum.bits.length ≤ B
  conditionDen : D.conditionDen.bits.length ≤ B
  epsilonNum : D.epsilonNum.bits.length ≤ B
  epsilonDen : D.epsilonDen.bits.length ≤ B
  alphaNum : D.alphaNum.bits.length ≤ B
  alphaDen : D.alphaDen.bits.length ≤ B
  tauNum : D.tauNum.bits.length ≤ B
  tauDen : D.tauDen.bits.length ≤ B
  span : ∀j,(D.span j).bits.length ≤ B

def inputWidth (N B : ℕ) : ℕ := 2^N+B+1030
def width (N B : ℕ) : ℕ := 2^formulas.length*(inputWidth N B+1)

theorem inputs_width (D : Data) (k N B : ℕ) (hk : k ≤ N) (hD : D.Width B) (i : ℕ) :
    (inputs D k i).bits.length  ≤  inputWidth N B := by
  have hpowpos : 0<(2:ℕ)^N := Nat.two_pow_pos N
  have hb : B  ≤  inputWidth N B := by unfold inputWidth;omega
  have hp : 2^k ≤ 2^N := Nat.pow_le_pow_right (by decide) hk
  have hd : (2^k).bits.length  ≤  inputWidth N B := by
    have h := Nat.lt_two_pow_self (n:=k)
    rw [Nat.size_eq_bits_len,Nat.size_pow]
    unfold inputWidth
    omega
  have hq : ((2^k)/slowDivisor).bits.length  ≤  inputWidth N B := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le_size (Nat.div_le_self _ _)).trans (by simpa only [Nat.size_eq_bits_len] using hd)
  have hdecay : (2^((2^k)/slowDivisor)).bits.length  ≤  inputWidth N B := by
    have hq := Nat.div_le_self (2^k) slowDivisor
    rw [Nat.size_eq_bits_len,Nat.size_pow]
    unfold inputWidth
    omega
  have h35 : (2^35:ℕ).bits.length  ≤  inputWidth N B := by
    rw [Nat.size_eq_bits_len,Nat.size_pow]
    unfold inputWidth
    omega
  have h1024 : slowDivisor.bits.length  ≤  inputWidth N B := by
    rw [slowDivisor,Nat.size_eq_bits_len,Nat.size_pow]
    unfold inputWidth
    omega
  have branch (p : Prop) [Decidable p] (a b : ℕ)
      (ha : a.bits.length ≤ inputWidth N B) (hb : b.bits.length ≤ inputWidth N B) :
      (if p then a else b).bits.length ≤ inputWidth N B := by
    split_ifs <;> assumption
  simp only [inputs]
  repeat' first
    | apply branch
    | exact hD.constant.trans hb | exact hD.length.trans hb
    | exact hD.wells.trans hb | exact hD.sourceSize.trans hb
    | exact hD.conditionNum.trans hb | exact hD.conditionDen.trans hb
    | exact hD.epsilonNum.trans hb | exact hD.epsilonDen.trans hb
    | exact hD.alphaNum.trans hb | exact hD.alphaDen.trans hb
    | exact hD.tauNum.trans hb | exact hD.tauDen.trans hb
    | exact (hD.span _).trans hb
    | exact hd | exact hq | exact hdecay | exact h35 | exact h1024
    | (change 1  ≤  inputWidth N B;unfold inputWidth;omega)
    | (change 2  ≤  inputWidth N B;unfold inputWidth;omega)
    | (change 3  ≤  inputWidth N B;unfold inputWidth;omega)
    | (change 0  ≤  inputWidth N B;omega)

theorem formulas_literals (B : ℕ) : ∀ a ∈ formulas,a.literalWidth ≤ B := by
  simp [formulas,boxFormulas,sizeFormulas,powerFormulas,fractionFormulas,productFormulas,NatAssign.Instruction.literalWidth]

theorem values_width (D : Data) (k N B : ℕ) (hk : k ≤ N) (hD : D.Width B)
    (i : ℕ) (hi : i∈ids) : (values D k i).bits.length ≤ width N B := by
  have h := NatAssign.values_width ids formulas formulas_valid (inputs D k) (inputWidth N B)
    (fun j _ => inputs_width D k N B hk hD j) (formulas_literals _) i hi
  exact (Nat.le_add_right _ 1).trans h

theorem width_pos (N B : ℕ) : 0<width N B := by unfold width;positivity

#print axioms values_width
end Maxwell.Continuum.Parameters.BufferMachine
