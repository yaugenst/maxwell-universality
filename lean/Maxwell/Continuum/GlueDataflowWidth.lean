import Maxwell.Continuum.GlueDataflowCost

/-! Raw numerator and denominator widths of the actual signed glue output.
The bound is independent of unrelated words in the surrounding bank. -/
namespace Maxwell.Continuum.RationalDataflow.Glue
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000

theorem result_width (N B : ℕ) (x : Parts) (hx : x.Width B) :
    (result N x).Width (2^28*(N+B+9)^4) := by
  have h1 : 1≤2^28*(N+B+9)^4 := by
    have hpow : 1≤(N+B+9)^4 := one_le_pow₀ (by omega)
    omega
  have hz : (Parts.literal 0).Width (2^28*(N+B+9)^4) := by
    exact (show (Parts.literal 0).Width 1 by change 0≤1 ∧ 0≤1 ∧ 1≤1;omega).mono h1
  have hm : (Phase.magnitude x).bits.length≤B+1 :=
    (IntegerNormSquare.magnitude_bits_length_le _ _).trans
      (Nat.add_le_add_right (max_le hx.1 hx.2.1) 1)
  have hd : x.denominator.bits.length≤B+1 := hx.2.2.trans (by omega)
  unfold result GlueMachine.Runtime.result
  split_ifs
  · exact hz
  · exact hz
  · apply (GlueMachine.Runtime.expResult_width _ _ N (B+1) hm hd).mono
    apply (GlueMachine.Runtime.resultWidth_bound N (B+1)).trans
    simpa only [Nat.add_assoc] using Nat.mul_le_mul_right ((N+B+9)^4) (show 2^27≤2^28 by norm_num)

#print axioms result_width
end Maxwell.Continuum.RationalDataflow.Glue
