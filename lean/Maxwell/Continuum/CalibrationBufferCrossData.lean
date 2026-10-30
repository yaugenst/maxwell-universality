import Maxwell.Continuum.CalibrationBufferNormData

/-! The two actual alternating power buffers encode both operands of a
quadratic pairing after a single matrix application. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferCross

open Maxwell.Cost Maxwell.Cost.CalibrationMatrix
open scoped BigOperators

def left {n : ℕ} (b : Buffers n) : Channels n :=
  ⟨fun i => addressValue (b.positive.get i),fun i => addressValue (b.negative.get i)⟩

def data {n : ℕ} (b : Buffers n) : CalibrationMatrix.Data n n :=
  ⟨b.data.width,b.data.clock,b.output.positiveBase,b.output.negativeBase,
    b.data.vectorPositiveBase,b.data.vectorNegativeBase,b.positive,b.negative,
    b.data.vectorPositive,b.data.vectorNegative,b.data.width_nonempty,b.data.clock_length⟩

theorem decodes {n : ℕ} (b : Buffers n) : Pairing.Decodes (data b) (left b) (bufferChannels b) :=
  ⟨fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

theorem left_advance {n : ℕ} (b : Buffers n) : left b.advance=bufferChannels b := rfl

theorem sized {n B : ℕ} (b : Buffers n) (h : b.Sized B) :
    (data b).Sized (NeumannMachine.StoredPairing.workWidth n B) := by
  have hc : B≤NeumannMachine.StoredPairing.workWidth n B := by
    unfold NeumannMachine.StoredPairing.workWidth
    omega
  exact ⟨h.1.1.trans hc,h.1.2.1.trans hc,h.2.1.trans hc,h.2.2.trans hc,
    h.1.2.2.2.2.1.trans hc,h.1.2.2.2.2.2.trans hc⟩

theorem represented_width {n B : ℕ} (b : Buffers n) {s : BitRAMState}
    (hsize : b.Sized B) (hs : Stored b.data s)
    (ho : OutputStored b.output (addressValue b.data.width) [] b.positive b.negative s) :
    (Pairing.positive (left b) (bufferChannels b)).bits.length≤NeumannMachine.StoredPairing.workWidth n B ∧
    (Pairing.negative (left b) (bufferChannels b)).bits.length≤NeumannMachine.StoredPairing.workWidth n B := by
  have old (i : Fin n) : (left b).positive i≤2^B ∧ (left b).negative i≤2^B := by
    constructor
    · have h := IndexedAddress.value_lt_pow_length (b.positive.get i)
      rw [ho.positive.length i] at h
      exact h.le.trans (Nat.pow_le_pow_right (by decide) hsize.1.2.1)
    · have h := IndexedAddress.value_lt_pow_length (b.negative.get i)
      rw [ho.negative.length i] at h
      exact h.le.trans (Nat.pow_le_pow_right (by decide) hsize.1.2.1)
  have current (i : Fin n) : (bufferChannels b).positive i≤2^B ∧ (bufferChannels b).negative i≤2^B := by
    constructor
    · have h := IndexedAddress.value_lt_pow_length (b.data.vectorPositive.get i)
      rw [hs.vectorPositive.length i] at h
      exact h.le.trans (Nat.pow_le_pow_right (by decide) hsize.1.2.1)
    · have h := IndexedAddress.value_lt_pow_length (b.data.vectorNegative.get i)
      rw [hs.vectorNegative.length i] at h
      exact h.le.trans (Nat.pow_le_pow_right (by decide) hsize.1.2.1)
  exact NeumannMachine.StoredPairing.pair_width _ _ old current

theorem rational_value {n : ℕ} (b : Buffers n) (D E : ℚ) :
    ((Pairing.positive (left b) (bufferChannels b):ℚ)-Pairing.negative (left b) (bufferChannels b))/(D*E)=
      ∑ i, (((left b).value i:ℚ)/D)*(((bufferChannels b).value i:ℚ)/E) := by
  have h := congrArg (fun z : ℤ => (z:ℚ)) (Pairing.signed_value (left b) (bufferChannels b))
  simp only [Int.cast_sub,Int.cast_natCast,Int.cast_sum,Int.cast_mul] at h
  rw [h,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms represented_width
#print axioms rational_value

end Maxwell.Continuum.Calibration.PowerMachine.BufferCross
