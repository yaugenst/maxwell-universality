import Maxwell.Continuum.CalibrationPowerInitialized
import Maxwell.Continuum.CalibrationStoredPairingData

/-! Exact squared norm of the current integer matrix-power buffer. The
representation works after either parity of the physical buffer swaps. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferNorm

open Maxwell.Cost Maxwell.Cost.CalibrationMatrix
open scoped BigOperators

def data {n : ℕ} (b : Buffers n) : CalibrationMatrix.Data n n :=
  ⟨b.data.width,b.data.clock,b.data.vectorPositiveBase,b.data.vectorNegativeBase,
    b.data.vectorPositiveBase,b.data.vectorNegativeBase,b.data.vectorPositive,
    b.data.vectorNegative,b.data.vectorPositive,b.data.vectorNegative,
    b.data.width_nonempty,b.data.clock_length⟩

theorem decodes {n : ℕ} (b : Buffers n) : Pairing.Decodes (data b) (bufferChannels b) (bufferChannels b) :=
  ⟨fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

theorem sized {n B : ℕ} (b : Buffers n) (h : b.Sized B) :
    (data b).Sized (NeumannMachine.StoredPairing.workWidth n B) := by
  have hc : B≤NeumannMachine.StoredPairing.workWidth n B := by
    unfold NeumannMachine.StoredPairing.workWidth; omega
  exact ⟨h.1.1.trans hc,h.1.2.1.trans hc,h.1.2.2.2.2.1.trans hc,
    h.1.2.2.2.2.2.trans hc,h.1.2.2.2.2.1.trans hc,h.1.2.2.2.2.2.trans hc⟩

theorem represented_width {n B : ℕ} (b : Buffers n) {s : BitRAMState}
    (hsize : b.Sized B) (hs : Stored b.data s) :
    (Pairing.positive (bufferChannels b) (bufferChannels b)).bits.length≤
        NeumannMachine.StoredPairing.workWidth n B ∧
      (Pairing.negative (bufferChannels b) (bufferChannels b)).bits.length≤
        NeumannMachine.StoredPairing.workWidth n B := by
  have raw (i : Fin n) : (bufferChannels b).positive i≤2^B ∧
      (bufferChannels b).negative i≤2^B := by
    constructor
    · have h := IndexedAddress.value_lt_pow_length (b.data.vectorPositive.get i)
      rw [hs.vectorPositive.length i] at h
      exact h.le.trans (Nat.pow_le_pow_right (by decide) hsize.1.2.1)
    · have h := IndexedAddress.value_lt_pow_length (b.data.vectorNegative.get i)
      rw [hs.vectorNegative.length i] at h
      exact h.le.trans (Nat.pow_le_pow_right (by decide) hsize.1.2.1)
  exact NeumannMachine.StoredPairing.pair_width _ _ raw raw

theorem norm_value {n : ℕ} (b : Buffers n) :
    (Pairing.positive (bufferChannels b) (bufferChannels b):ℤ)-
      Pairing.negative (bufferChannels b) (bufferChannels b)=
        ∑ i, ((bufferChannels b).value i)^2 := by
  rw [Pairing.signed_value]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rational_norm_value {n : ℕ} (b : Buffers n) (D : ℕ) :
    (((Pairing.positive (bufferChannels b) (bufferChannels b):ℤ)-
      Pairing.negative (bufferChannels b) (bufferChannels b):ℤ):ℚ)/(D:ℚ)^2=
        ∑ i, (((bufferChannels b).value i:ℚ)/D)^2 := by
  rw [norm_value]
  simp only [Int.cast_sum,Int.cast_pow,Finset.sum_div,div_pow]

#print axioms represented_width
#print axioms rational_norm_value

end Maxwell.Continuum.Calibration.PowerMachine.BufferNorm
