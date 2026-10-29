import Maxwell.Cost.PositiveGraph.Metadata
import Maxwell.Cost.Structured.NatAssign.Bounds

namespace Maxwell.Cost.PositiveGraph.Metadata
open Structured

theorem price_bound (width dimension count : ℕ)
    (hd : dimension < 2^width) (hc : count < 2^(width+3)) :
    price width dimension count ≤ (3000*8^statements.length+100)*(width+6)^2 := by
  have hw : width.bits.length ≤ width := by
    simpa only [WordLength.countBits_eq] using WordLength.countBits_length width
  have hdim : dimension.bits.length ≤ width := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hd
  have hcount : count.bits.length ≤ width+3 := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hc
  have hbank : ∀ i ∈ ids, (initial width dimension count i).bits.length ≤ width+4 := by
    intro i _
    simp only [initial]
    split_ifs <;> first | omega | simp
  have hliteral : ∀ a ∈ statements, a.literalWidth ≤ width+4 := by
    simp [statements,NatAssign.Instruction.literalWidth]
    change 2 ≤ width+4 ∧ 3 ≤ width+4 ∧ 4 ≤ width+4 ∧ 2 ≤ width+4
    omega
  have hp := NatAssign.price_bound ids statements valid (initial width dimension count)
    (width+4) hbank hliteral
  change numericPrice width dimension count ≤ 3000*8^statements.length*(width+4+2)^2 at hp
  have hlinear : 55*width+93 ≤ 100*(width+6)^2 := by nlinarith
  dsimp [price]
  nlinarith only [hp,hlinear]

end Maxwell.Cost.PositiveGraph.Metadata
