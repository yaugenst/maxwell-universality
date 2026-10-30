import Maxwell.Continuum.ParameterIterations
import Maxwell.Continuum.ParameterPowerMachine

/-! The stored-exponent power primitive has polynomial bit-operation cost.
The exponent controls a counted loop in one fixed machine program. -/

namespace Maxwell.Continuum.Parameters
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
namespace PowerMachine
open Maxwell.Cost.SelectedParameters.DynamicPower

theorem cost_polynomial (N B : ℕ) : costBound N B ≤ 2^24*(N+1)^3*(B+2)^2 := by
  unfold costBound bodyCost width
  norm_num
  ring_nf
  omega

theorem executes_polynomial (v : ℕ → ℕ) (N B : ℕ) (hB : 1 ≤ B)
    (hw : ∀ i ∈ ids, (v i).bits.length ≤ B) (hN : N.bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hsc : NatAssign.Scratch s.val)
    (hn : Word s.val 534 N) :
    ∃ cost t, Executes input tape code cost s t ∧ cost ≤ 2^24*(N+1)^3*(B+2)^2 ∧
      Ready (v 530) (v 531) N t ∧ Blank t.val 534 ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost, t, he, hc, hr, hb, hf⟩ := executes v N B hB hw hN input tape s hs hsc hn
  exact ⟨cost, t, he, hc.trans (cost_polynomial N B), hr, hb, hf⟩

theorem cost_of_polylog_arguments {N B C ℓ : ℕ} (hℓ : 0 < ℓ)
    (hN : N ≤ C*ℓ^6) (hB : B ≤ C*ℓ^6) :
    costBound N B ≤ 2^24*(C+1)^3*(C+2)^2*ℓ^30 := by
  have hl : 1 ≤ ℓ^6 := one_le_pow₀ (by omega : 1 ≤ ℓ)
  have hN' : N+1 ≤ (C+1)*ℓ^6 := by nlinarith only [hN, hl]
  have hB' : B+2 ≤ (C+2)*ℓ^6 := by nlinarith only [hB, hl]
  calc
    _ ≤ 2^24*(N+1)^3*(B+2)^2 := cost_polynomial N B
    _ ≤ 2^24*((C+1)*ℓ^6)^3*((C+2)*ℓ^6)^2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN' 3))
        (Nat.pow_le_pow_left hB' 2)
    _ = _ := by ring

#print axioms executes_polynomial
#print axioms cost_of_polylog_arguments

end PowerMachine
end Maxwell.Continuum.Parameters
