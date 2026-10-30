import Maxwell.Continuum.CalibrationNormalizationOutput
import Maxwell.Continuum.CalibrationGlobalNormalization

/-! The output table of the executed normalization is the literal finite
Fourier mode, including its exact coefficient array and normalization. -/

namespace Maxwell.Continuum.Calibration.GlobalPower

open Maxwell.Cost Maxwell.Cost.CalibrationMatrix
open RationalDataflow RationalDataflow.PartArray
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] modeRadius modeMatrix FiniteAlgorithm.precision
  FiniteAlgorithm.iterations FiniteAlgorithm.seed FiniteAlgorithm.rawMode
  PowerMachine.rationalPower sqrtRationalCenter

def tableData (R : ℕ) (b : Table (2*aliasArraySize R)) : FourierData :=
  ⟨R,unpack R (fun i => (b.get i).value)⟩

theorem arrayNormCenter_eq {n : ℕ} (a : Buffers n) (D K P : ℕ) (x : Fin n → ℚ)
    (hx : ∀ i, ((PowerMachine.bufferChannels a).value i:ℚ)/(D^(K+1):ℕ)=x i) :
    PowerMachine.BufferNorm.arrayNormCenter a D K P=sqrtRationalCenter (∑ i,x i^2) P := by
  unfold PowerMachine.BufferNorm.arrayNormCenter
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by rw [hx i])

theorem buffer_normCenter (L r N : ℕ) (z : ℚ)
    (a : Buffers (2*aliasArraySize (modeRadius L r N))) (D : ℕ)
    (hbuffer : ∀ i, ((PowerMachine.bufferChannels a).value i:ℚ)/(D^(FiniteAlgorithm.iterations N+1):ℕ)=
      PowerMachine.rationalPower (modeMatrix L r N z)
        (sample (modeRadius L r N) (FiniteAlgorithm.seed L r N).field) (FiniteAlgorithm.iterations N) i) :
    PowerMachine.BufferNorm.arrayNormCenter a D (FiniteAlgorithm.iterations N) (FiniteAlgorithm.precision L r N)=
      FourierData.normCenter (FiniteAlgorithm.precision L r N) (FiniteAlgorithm.rawMode L r N z) := by
  exact (arrayNormCenter_eq a D _ _ _ hbuffer).trans (rawMode_normCenter L r N z).symm

theorem output_mode (L r N : ℕ) (z : ℚ)
    (a : Buffers (2*aliasArraySize (modeRadius L r N)))
    (b : Table (2*aliasArraySize (modeRadius L r N))) (D : ℕ)
    (hbuffer : ∀ i, ((PowerMachine.bufferChannels a).value i:ℚ)/(D^(FiniteAlgorithm.iterations N+1):ℕ)=
      PowerMachine.rationalPower (modeMatrix L r N z)
        (sample (modeRadius L r N) (FiniteAlgorithm.seed L r N).field) (FiniteAlgorithm.iterations N) i)
    (houtput : ∀ i, (b.get i).value=
      (PowerMachine.BufferNorm.arrayNormCenter a D (FiniteAlgorithm.iterations N)
        (FiniteAlgorithm.precision L r N))⁻¹*
          (((PowerMachine.bufferChannels a).value i:ℚ)/(D^(FiniteAlgorithm.iterations N+1):ℕ))) :
    tableData (modeRadius L r N) b=FiniteAlgorithm.mode L r N z := by
  rw [←normalizedMode_eq]
  unfold rawModeData
  rw [←normalized_data]
  unfold tableData
  congr 2
  funext i
  rw [houtput i,buffer_normCenter L r N z a D hbuffer,hbuffer i,rawMode_normCenter]
  rfl

theorem actual_buffer_normCenter_pos {L : ℕ} (hL : MasterConstants.Ls≤(L:ℝ))
    (r N : ℕ) (z : ℚ) (calibration : Auxiliary.Calibration (L:ℝ)⁻¹ z)
    (a : Buffers (2*aliasArraySize (modeRadius L r N))) (D : ℕ)
    (hbuffer : ∀ i, ((PowerMachine.bufferChannels a).value i:ℚ)/(D^(FiniteAlgorithm.iterations N+1):ℕ)=
      PowerMachine.rationalPower (modeMatrix L r N z)
        (sample (modeRadius L r N) (FiniteAlgorithm.seed L r N).field) (FiniteAlgorithm.iterations N) i) :
    0<PowerMachine.BufferNorm.arrayNormCenter a D (FiniteAlgorithm.iterations N)
      (FiniteAlgorithm.precision L r N) := by
  rw [buffer_normCenter L r N z a D hbuffer]
  exact rawMode_normCenter_pos hL r N z calibration

#print axioms output_mode
#print axioms actual_buffer_normCenter_pos

end Maxwell.Continuum.Calibration.GlobalPower
