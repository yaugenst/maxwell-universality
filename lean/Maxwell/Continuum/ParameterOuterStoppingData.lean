import Maxwell.Continuum.ParameterBufferMachinePredicate
import Maxwell.Continuum.ParameterStoppingTests

/-! Literal operands for the two outer stopping comparisons. Leakage
reuses the exact buffer ratio; the tail uses a stored integer numerator. -/
namespace Maxwell.Continuum.Parameters.OuterStopping

def tailNumerator (C J L Z : ℕ) : ℕ := 4*J*C*L^5*Z^2

theorem tail_comparison (C J L Z e d : ℕ) (hC : C=2^e) (hZ : Z=3^d) :
    (tailNumerator C J L Z:ℚ) ≤ (2:ℚ)^(L/slowDivisor) ↔
      (J:ℚ)*(2:ℚ)^e*(L:ℚ)^5*rationalDecay L ≤ (zeta d)^2/4 := by
  have hp : (0:ℚ)<2^(L/slowDivisor) := by positivity
  have hz : (0:ℚ)<4*(3^d:ℚ)^2 := by positivity
  have hzeta : (zeta d)^2/4=1/(4*((3:ℚ)^d)^2) := by
    simp only [zeta,one_div,inv_pow]
    ring
  have hdecay : rationalDecay L=1/(2:ℚ)^(L/slowDivisor) := by
    simp [rationalDecay,one_div,inv_pow]
  rw [hzeta,hdecay,mul_one_div,div_le_div_iff₀ hp hz]
  simp only [tailNumerator,hC,hZ,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,one_mul]
  ring_nf

#print axioms tail_comparison
end Maxwell.Continuum.Parameters.OuterStopping
