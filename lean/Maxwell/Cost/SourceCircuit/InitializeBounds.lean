import Maxwell.Cost.SourceCircuit.Initialize

namespace Maxwell.Cost.SourceCircuit.Initialize

theorem rootBody_bound (W : ℕ) :
    initializeRootBodyCost W.bits [] ≤ 10000*(W+5)^2 := by
  have hbits : W.bits.length ≤ W := by
    simpa only [WordLength.countBits_eq] using WordLength.countBits_length W
  simp only [initializeRootBodyCost,BankArray.costCap,ArrayAccess.costCap,
    RationalAccumulator.address_bits,List.length_replicate,List.length_nil]
  have hsum : W.bits.length+W+0+5 ≤ 2*(W+5) := by omega
  have hsq := Nat.pow_le_pow_left hsum 2
  nlinarith only [hbits,hsq]

/-- Writing every root word and every countdown operation remains linear
in the original dimension, with an explicit quadratic logarithmic factor. -/
theorem price_bound (n m p : ℕ) (hn : n ≤ m) :
    price n m p ≤ 50000*(n+1)*(m.size+p.size+10)^2 := by
  let D := m.size+p.size+10
  let A := D^2
  have hD : 10 ≤ D := by dsimp [D]; omega
  have hDA : D ≤ A := by dsimp [A]; nlinarith
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hnsize : n.bits.length ≤ D := by
    rw [Nat.size_eq_bits_len]
    have hh := Nat.size_le_size hn
    dsimp [D]
    omega
  have hmsize : m.bits.length ≤ D := by rw [Nat.size_eq_bits_len]; dsimp [D]; omega
  have hbody := rootBody_bound (InitializeMetadata.width m p)
  have hw : InitializeMetadata.width m p+5 = D := by
    dsimp [InitializeMetadata.width,InitializeMetadata.exponent,D]
    omega
  rw [hw] at hbody
  have hb := Nat.mul_le_mul_left n hbody
  change n*initializeRootBodyCost (InitializeMetadata.width m p).bits [] ≤ n*(10000*A) at hb
  have hprefix : 20000*(m.size+p.size+6)^2 ≤ 20000*A := by
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [D]; omega) 2)
  have hcounter : (n+1)*(13*n.bits.length+15) ≤ 28*(n+1)*A := by
    have hh : 13*n.bits.length+15 ≤ 28*A := by omega
    simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_left (n+1) hh
  have hsmall : 6*n.bits.length+4+(15*m.bits.length+17) ≤ 42*A := by omega
  have htotal : A ≤ (n+1)*A := by nlinarith
  dsimp only [price]
  change _ ≤ 50000*(n+1)*A
  nlinarith only [hprefix,hcounter,hb,hsmall,htotal]

end Maxwell.Cost.SourceCircuit.Initialize
