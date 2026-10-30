import Maxwell.Continuum.CalibrationBufferNormalizedScale

/-! All normalization and output widths are polynomial expressions in the
original stored-buffer width, iteration count, and requested precision. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferNorm

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def outputWidth (n K P B : ℕ) : ℕ := 32*normalizationWidth n K P B+32*P+64
def boundedScaleCost (n K P B : ℕ) : ℕ :=
  normalizationCost n K P B+2^52*(outputWidth n K P B)^2

theorem denominatorPower_width (n D K P B : ℕ) (hD : D.bits.length≤B) :
    (D^(K+1)).bits.length≤normalizationWidth n K P B := by
  have h := NeumannMachine.DenominatorPower.denominator_width D K B hD
  unfold normalizationWidth
  omega

theorem arrayNormRadicand_width {n B : ℕ} (b : Buffers n) (D K P : ℕ)
    (hsize : b.Sized B) (hD : D.bits.length≤B) {s : BitRAMState}
    (hs : CalibrationMatrix.Stored b.data s) :
    (arrayNormRadicand b D K P).bits.length≤4*normalizationWidth n K P B+3*P+5 := by
  have hpair := represented_width b hsize hs
  have hw : NeumannMachine.StoredPairing.workWidth n B≤normalizationWidth n K P B := by
    unfold normalizationWidth
    omega
  exact Root.normRadicand_bits _ _ _ P _ (hpair.1.trans hw) (hpair.2.trans hw)
    (denominatorPower_width n D K P B hD)

theorem factor_cost_bound (n D K P B T den : ℕ)
    (hT : T.bits.length≤4*normalizationWidth n K P B+3*P+5)
    (hden : den.bits.length≤2*normalizationWidth n K P B+2*P+3)
    (hD : (D^(K+1)).bits.length≤normalizationWidth n K P B) :
    Factor.costBound T den (D^(K+1))≤2^52*(outputWidth n K P B)^2 := by
  unfold Factor.costBound
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  unfold outputWidth
  omega

theorem factor_output_width (n D K P B T den : ℕ)
    (hT : T.bits.length≤4*normalizationWidth n K P B+3*P+5)
    (hden : den.bits.length≤2*normalizationWidth n K P B+2*P+3)
    (hD : (D^(K+1)).bits.length≤normalizationWidth n K P B) (i : ℕ) :
    (Factor.outputValues T den (D^(K+1)) i).bits.length≤outputWidth n K P B := by
  have hdone := Factor.done_width T i
  have hsqrt : (Nat.sqrt T).bits.length≤T.bits.length := by
    rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
    exact Nat.size_le_size (Nat.sqrt_le_self T)
  have hproduct := RationalAccumulator.bits_mul_le (D^(K+1)) (Nat.sqrt T)
  have hz : (0:ℕ).bits.length=0 := rfl
  unfold Factor.outputValues Factor.inputValues outputWidth
  split_ifs <;> omega

theorem output_scale_guard {n B : ℕ} (b : Buffers n) (K P den : ℕ)
    (hsize : b.Sized B)
    (hden : den.bits.length≤2*normalizationWidth n K P B+2*P+3) :
    addressValue (data b).width+den.bits.length≤outputWidth n K P B := by
  have ha : addressValue (data b).width≤B := hsize.1.2.1
  have hB : B≤normalizationWidth n K P B := by
    unfold normalizationWidth NeumannMachine.StoredPairing.workWidth
    omega
  unfold outputWidth
  omega

theorem output_data_sized {n B : ℕ} (b : Buffers n) (K P : ℕ) (hsize : b.Sized B) :
    (data b).Sized (outputWidth n K P B) := by
  have h := sized b hsize
  have hw : NeumannMachine.StoredPairing.workWidth n B≤outputWidth n K P B := by
    unfold outputWidth normalizationWidth
    omega
  exact ⟨h.1.trans hw,h.2.1.trans hw,h.2.2.1.trans hw,h.2.2.2.1.trans hw,
    h.2.2.2.2.1.trans hw,h.2.2.2.2.2.trans hw⟩

#print axioms arrayNormRadicand_width
#print axioms factor_cost_bound
#print axioms factor_output_width

end Maxwell.Continuum.Calibration.PowerMachine.BufferNorm
