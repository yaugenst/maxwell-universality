import Maxwell.Continuum.ParameterSpacingMachineData
import Maxwell.Cost.Structured.NatAssign.Values
import Maxwell.Codec.NaturalLength

namespace Maxwell.Continuum.Parameters.SpacingMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

structure Data.Width (D : Data) (B : ℕ) : Prop where
  constant : D.constant.bits.length≤B
  length : D.length.bits.length≤B
  conditionNum : D.conditionNum.bits.length≤B
  conditionDen : D.conditionDen.bits.length≤B
  epsilonNum : D.epsilonNum.bits.length≤B
  epsilonDen : D.epsilonDen.bits.length≤B

def inputWidth (N B : ℕ) : ℕ := 4*2^N+B+1030
def width (N B : ℕ) : ℕ := 2^formulas.length*(inputWidth N B+1)

theorem inputs_width (D : Data) (k N B : ℕ) (hk : k≤N) (hD : D.Width B) (i : ℕ) :
    (inputs D k i).bits.length ≤ inputWidth N B := by
  have hb : B ≤ inputWidth N B := by unfold inputWidth;omega
  have hp : 2^k≤2^N := Nat.pow_le_pow_right (by decide) hk
  have hd : (2^k).bits.length ≤ inputWidth N B := by
    have h := Nat.lt_two_pow_self (n:=k)
    rw [Nat.size_eq_bits_len,Nat.size_pow]
    unfold inputWidth
    omega
  have h3 : (3^(2^k)).bits.length ≤ inputWidth N B := by
    have h := Codec.power_bits_le 3 (2^k)
    have hb3 : (3:ℕ).bits.length=2 := rfl
    rw [hb3] at h
    unfold inputWidth
    omega
  have h8 : (8^(2^k)).bits.length ≤ inputWidth N B := by
    have h := Codec.power_bits_le 8 (2^k)
    have hb8 : (8:ℕ).bits.length=4 := rfl
    rw [hb8] at h
    unfold inputWidth
    omega
  have h24 : (2^24:ℕ).bits.length ≤ inputWidth N B := by
    rw [Nat.size_eq_bits_len,Nat.size_pow]
    unfold inputWidth
    omega
  have h1026 : (2^1026:ℕ).bits.length ≤ inputWidth N B := by
    rw [Nat.size_eq_bits_len,Nat.size_pow]
    unfold inputWidth
    omega
  simp only [inputs]
  split_ifs <;> first
    | exact hD.constant.trans hb | exact hD.length.trans hb
    | exact hD.conditionNum.trans hb | exact hD.conditionDen.trans hb
    | exact hD.epsilonNum.trans hb | exact hD.epsilonDen.trans hb
    | exact hd | exact h3 | exact h8 | exact h24 | exact h1026
    | (change 1 ≤ inputWidth N B;unfold inputWidth;omega) | simp

theorem formulas_literals (B : ℕ) : ∀ a ∈ formulas, a.literalWidth≤B := by
  simp [formulas,NatAssign.Instruction.literalWidth]

theorem values_width (D : Data) (k N B : ℕ) (hk : k≤N) (hD : D.Width B)
    (i : ℕ) (hi : i∈ids) : (values D k i).bits.length≤width N B := by
  have h := NatAssign.values_width ids formulas formulas_valid (inputs D k) (inputWidth N B)
    (fun j _ => inputs_width D k N B hk hD j) (formulas_literals _) i hi
  exact (Nat.le_add_right _ 1).trans h

theorem width_pos (N B : ℕ) : 0<width N B := by unfold width;positivity

#print axioms values_width

end Maxwell.Continuum.Parameters.SpacingMachine
